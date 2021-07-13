// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public
// License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of
// proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tbox.impl;

import static com.clarkparsia.pellet.utils.TermFactory.BOTTOM;
import static com.clarkparsia.pellet.utils.TermFactory.TOP;
import static com.clarkparsia.pellet.utils.TermFactory.and;
import static com.clarkparsia.pellet.utils.TermFactory.inv;
import static com.clarkparsia.pellet.utils.TermFactory.not;
import static com.clarkparsia.pellet.utils.TermFactory.some;
import static com.clarkparsia.pellet.utils.TermFactory.term;
import static org.mindswap.pellet.utils.ATermUtils.isAnd;
import static org.mindswap.pellet.utils.ATermUtils.isHasValue;
import static org.mindswap.pellet.utils.ATermUtils.isNegatedPrimitive;
import static org.mindswap.pellet.utils.ATermUtils.isNominal;
import static org.mindswap.pellet.utils.ATermUtils.isNot;
import static org.mindswap.pellet.utils.ATermUtils.isOneOf;
import static org.mindswap.pellet.utils.ATermUtils.isOr;
import static org.mindswap.pellet.utils.ATermUtils.isSomeValues;
import static org.mindswap.pellet.utils.ATermUtils.negate;
import static org.mindswap.pellet.utils.ATermUtils.nnf;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.mindswap.pellet.*;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tbox.TBox;
import org.mindswap.pellet.utils.ATermUtils;
import org.mindswap.pellet.utils.BinarySet;
import org.mindswap.pellet.utils.Namespaces;
import org.mindswap.pellet.utils.iterator.IteratorUtils;
import org.mindswap.pellet.utils.iterator.MultiIterator;
import org.mindswap.pellet.utils.iterator.MultiListIterator;

import aterm.AFun;
import aterm.ATermAppl;
import aterm.ATermList;

import com.clarkparsia.pellet.datatypes.Facet;
import com.clarkparsia.pellet.utils.CollectionUtils;
import com.clarkparsia.pellet.utils.MultiMapUtils;

/**
 * TBox implementation that keeps track of explanations and allows flexible absorption
 * algorithms.
 * 
 * @author Evren Sirin
 */
public class TBoxImpl implements TBox {
	public static final Logger log = Logger.getLogger(TBoxImpl.class.getName());
	
	protected static final Map<ATermAppl,String> FACETS;
	static {
		FACETS = new HashMap<ATermAppl,String>();
		FACETS.put( Facet.XSD.MIN_INCLUSIVE.getName(), Namespaces.SWRLB + "greaterThanOrEqual" );
		FACETS.put( Facet.XSD.MIN_EXCLUSIVE.getName(), Namespaces.SWRLB + "greaterThan" );
		FACETS.put( Facet.XSD.MAX_INCLUSIVE.getName(), Namespaces.SWRLB + "lessThanOrEqual" );
		FACETS.put( Facet.XSD.MAX_EXCLUSIVE.getName(), Namespaces.SWRLB + "lessThan" );
	}
	
	private static final Set<Set<ATermAppl>>	SINGLE_EMPTY_SET	= Collections
																			.singleton( Collections
																					.<ATermAppl> emptySet() );

	protected KnowledgeBase kb;

	protected Set<ATermAppl> classes = CollectionUtils.makeIdentitySet();
	private Set<ATermAppl> allClasses;

	/**
	 * MultiValueMap where key is an axiom and the values are the explanations
	 * of the key
	 */
	private Map<ATermAppl, Set<Set<ATermAppl>>>	tboxAxioms			= CollectionUtils
																			.makeIdentityMap();
	/**
	 * MultiValueMap where key is an axiom and the values are axioms for which
	 * the key is a part of an explanation
	 */
	private Map<ATermAppl, Set<ATermAppl>>		reverseExplain		= CollectionUtils
																			.makeIdentityMap();

	private Set<ATermAppl>						tboxAssertedAxioms	= CollectionUtils
																			.makeIdentitySet();
	 

	private Set<ATermAppl>						absorbedAxioms		= CollectionUtils.makeSet();
		
	private PrimitiveTBox primitiveTbox;
	private UnaryTBox unaryTbox;
	private BinaryTBox binaryTbox;

	public TBoxImpl(KnowledgeBase kb) {
		this.kb = kb;
		
		primitiveTbox = new PrimitiveTBox();
		unaryTbox = new UnaryTBox();
		binaryTbox = new BinaryTBox();
	}

	public KnowledgeBase getKB() {
		return kb;
	}
	
	public Set<ATermAppl> getAllClasses() {
		if( allClasses == null ) {
			allClasses = new HashSet<ATermAppl>( classes );
			allClasses.add( ATermUtils.TOP );
			allClasses.add( ATermUtils.BOTTOM );
		}
		return allClasses;
	}

	public Set<Set<ATermAppl>> getAxiomExplanations(ATermAppl axiom) {
		return tboxAxioms.get( axiom );
	}

	public Set<ATermAppl> getAxiomExplanation(ATermAppl axiom) {
		Set<Set<ATermAppl>> explains = tboxAxioms.get( axiom );

		if( explains == null || explains.isEmpty() ) {
			log.warning( "No explanation for " + axiom );
			return Collections.emptySet();
		}

		// we won't be generating multiple explanations using axiom
		// tracing so we just pick one explanation. the other option
		// would be to return the union of all explanations which
		// would cause Pellet to return non-minimal explanations sets
		for ( Set<ATermAppl> explain : explains ) {
			return explain;
		}
		return Collections.emptySet();
	}

	/**
	 * Add a new explanation for the given axiom. If a previous explanation
	 * exists this will be stored as another explanation.
	 * 
	 * @param axiom
	 * @param explain
	 * @return
	 */
	protected boolean addAxiomExplanation(ATermAppl axiom, Set<ATermAppl> explain) {
		if( log.isLoggable( Level.FINE ) )
			log.fine( "Add Axiom: " + ATermUtils.toString( axiom ) + " Explanation: " + explain );

		boolean added = false;
		if( !PelletOptions.USE_TRACING ) {
			added = tboxAxioms.put( axiom, SINGLE_EMPTY_SET ) == null;
		}
		else {
			added = MultiMapUtils.add( tboxAxioms, axiom, explain );
		}

		if( added ) {
			for( ATermAppl explainAxiom : explain ) {
				if( !axiom.equals( explainAxiom ) )
					MultiMapUtils.add( reverseExplain, explainAxiom, axiom );
			}
		}

		return added;
	}
	
	private static List<ATermAppl> normalizeDisjointAxiom(ATermAppl... concepts) {
		List<ATermAppl> axioms = CollectionUtils.makeList();	
		
		for( int i = 0; i < concepts.length - 1; i++ ) {
			ATermAppl c1 = concepts[i];
			ATermAppl notC1 = ATermUtils.makeNot( c1 );	
			for( int j = i + 1; j < concepts.length; j++ ) {
				ATermAppl c2 = concepts[j];				
				ATermAppl notC2 = ATermUtils.makeNot( c2 );
				
				axioms.add( ATermUtils.makeSub( c1, notC2 ) );
				if( ATermUtils.isPrimitive( c2 ) ) {	
					axioms.add( ATermUtils.makeSub( c2, notC1 ) );
				}
			}
		}
				
		return axioms;
	}

	public boolean addAxiom(ATermAppl axiom) {
		tboxAssertedAxioms.add( axiom );
		
		List<ATermAppl> axioms = null;

		Set<ATermAppl> explain = PelletOptions.USE_TRACING
			? Collections.singleton( axiom )
			: Collections.<ATermAppl>emptySet();
		
		if( axiom.getAFun().equals( ATermUtils.EQCLASSFUN ) ) {
			axioms = Collections.singletonList( axiom );
		}
		else if( axiom.getAFun().equals( ATermUtils.SUBFUN ) ) {
			axioms = Collections.singletonList( axiom );
		}
		else if( axiom.getAFun().equals( ATermUtils.DISJOINTFUN ) ) {
			ATermAppl c1 = (ATermAppl) axiom.getArgument( 0 );
			ATermAppl c2 = (ATermAppl) axiom.getArgument( 1 );
			
			axioms = normalizeDisjointAxiom(c1, c2);
		}
		else if( axiom.getAFun().equals( ATermUtils.DISJOINTSFUN ) ) {
			ATermList list = (ATermList) axiom.getArgument( 0 );	
			ATermAppl[] concepts = ATermUtils.toArray( list );
			
			axioms = normalizeDisjointAxiom(concepts);
		}
		else {
			log.warning( "Not a valid TBox axiom: " + axiom );
			return false;
		}

		boolean added = false;
		for( ATermAppl a : axioms ) {
			added |= addAxiom( a, explain, false );
		}
		
		return added;
	}

	protected boolean addAxiom(ATermAppl axiom, Set<ATermAppl> explanation, boolean forceAddition) {
		boolean added = addAxiomExplanation( axiom, explanation );

		if( added || forceAddition ) {
			if( axiom.getAFun().equals( ATermUtils.EQCLASSFUN ) ) {
				ATermAppl c1 = (ATermAppl) axiom.getArgument( 0 );
				ATermAppl c2 = (ATermAppl) axiom.getArgument( 1 );
			
				boolean def = false;
				if( ATermUtils.isPrimitive( c1 ) 
						&& !unaryTbox.unfold( c1 ).hasNext()
						&& !binaryTbox.unfold( c1 ).hasNext() ) {
					def = primitiveTbox.add( c1, c2, explanation );
				}
				
				if( !def 
						&& ATermUtils.isPrimitive( c2 ) 
						&& !unaryTbox.unfold( c2 ).hasNext()
						&& !binaryTbox.unfold( c2 ).hasNext() ) {
					def = primitiveTbox.add( c2, c1, explanation );
				}					
				
				if( !def ) {
					absorbSubClass( c1, c2, explanation );
					absorbSubClass( c2, c1, explanation );
				}				
			}
			else if( axiom.getAFun().equals( ATermUtils.SUBFUN ) ) {
				ATermAppl sub = (ATermAppl) axiom.getArgument( 0 );
				ATermAppl sup = (ATermAppl) axiom.getArgument( 1 );

				absorbSubClass( sub, sup, explanation );
			}
		}

		return added;
	}
	
	private void absorbSubClass(ATermAppl sub, ATermAppl sup, Set<ATermAppl> explanation) {
		if( log.isLoggable( Level.FINE ) ) 
			log.fine( "Absorb: subClassOf(" + ATermUtils.toString(sub) + ", " + ATermUtils.toString(sup) + ")");
			
		Set<ATermAppl> terms = CollectionUtils.makeSet();
		terms.add( nnf( sub ) );				
		terms.add( nnf( negate( sup ) ) );

		absorbAxiom( terms, CollectionUtils.makeSet( explanation ) );
	}
	
	private Absorption[] absorptions = {
		new BinaryAbsorption( true ), 
		new DeterministicUnaryAbsorption(),
		new SimplifyAbsorption(),
		new OneOfAbsorption(),
		new HasValueAbsorption(),
		new BinaryAbsorption( false ), 
		new ExistentialAbsorption(),
		new UnaryAbsorption(), 
		new UnfoldAbsorption(),
		new DomainAbsorption(), 
		new GeneralAbsorption() 
	};
	
	private void absorbAxiom(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
		if( terms.size() == 1 ) {
			unaryTbox.add( TOP, not( terms.iterator().next() ), explanation );
			return;
		}
			
		for( Absorption absorption : absorptions ) {
			if( absorption.absorb( terms, explanation ) )
				return;
		}
		
		throw new InternalReasonerException( "Absorption failed");
	}
	

	protected ATermAppl disjunction(Set<ATermAppl> terms) {		
		return not( and( terms.toArray( new ATermAppl[ terms.size() ] ) ) );
	}
	
	private interface Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation);
		
	}
	
	private class SimplifyAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			Iterator<ATermAppl> i = terms.iterator();
			while( i.hasNext() ) {
				ATermAppl term = i.next();
//				if( isNot( term ) ) {
//					ATermAppl nnf = nnf( term );
//					if( term.equals( nnf ) )
//						continue;
//					i.remove();
//					terms.add( nnf );
//					absorbAxiom( terms, explanation );
//					return true;
//				}
				 
				if( isAnd( term ) ) {
					i.remove();
					for( ATermList list = (ATermList) term.getArgument( 0 ) ; !list.isEmpty(); list = list.getNext() ) {
						terms.add( (ATermAppl) list.getFirst() );					
					}
					absorbAxiom( terms, explanation );
					return true;
				}
				
				if( isOr( term ) ) {
					i.remove();
					for( ATermList list = (ATermList) term.getArgument( 0 ); !list.isEmpty(); list = list.getNext() ) {
						Set<ATermAppl> newTerms = CollectionUtils.makeSet( terms );
						newTerms.add( (ATermAppl) list.getFirst() );
						absorbAxiom( newTerms, explanation );	
					}
					return true;
				}
			}
			return false;
		}
	}
	
	private class OneOfAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			if( !PelletOptions.USE_NOMINAL_ABSORPTION )
				return false;
			
			for( ATermAppl term : terms ) {
				Iterator<ATermAppl> nominals = getNominals( term );
				
				if( nominals.hasNext() ) {
					terms.remove( term );

					ATermAppl c = disjunction( terms );

					absorbOneOf( nominals, c, explanation );

					return true;
				}				
			}
			return false;
		}
		
		public Iterator<ATermAppl> getNominals(ATermAppl term) {
			if( isOneOf( term ) ) {
				ATermList list = (ATermList) term.getArgument( 0 );
				return new MultiListIterator( list );
			}
			else if( isNominal( term ) ) {
				return IteratorUtils.singletonIterator( term );
			}
			
			return IteratorUtils.emptyIterator();
		}

		private void absorbOneOf(Iterator<ATermAppl> list, ATermAppl c, Set<ATermAppl> explain) {
			if( PelletOptions.USE_PSEUDO_NOMINALS ) {
				if( log.isLoggable( Level.WARNING ) )
					log.warning( "Ignoring axiom involving nominals: " + explain );
				return;
			}

			absorbedAxioms.addAll( explain );

			TimeDS ds = new TimeDS( explain );
			while( list.hasNext() ) {
				ATermAppl nominal = list.next();			
				ATermAppl ind = (ATermAppl) nominal.getArgument( 0 );

				if( log.isLoggable( Level.FINE ) )
					log.fine( "Absorb nominals: " + ATermUtils.toString( c ) + " " +  ind );
				
				kb.addIndividual( ind );
				kb.addType( ind, c, ds );
			}
		}
	}

	private class HasValueAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			if( !PelletOptions.USE_HASVALUE_ABSORPTION )
				return false;
			
			for( Iterator<ATermAppl> i = terms.iterator(); i.hasNext(); ) {
				ATermAppl term = i.next();
				if( isHasValue( term ) ) {
					ATermAppl p = (ATermAppl) term.getArgument( 0 );
					if( !kb.isObjectProperty( p ) )
						continue;

					i.remove();
					ATermAppl c = disjunction( terms );

					ATermAppl nominal = (ATermAppl) term.getArgument( 1 );
					ATermAppl ind = (ATermAppl) nominal.getArgument( 0 );

					ATermAppl invP = kb.getProperty( p ).getInverse().getName();
					ATermAppl allInvPC = ATermUtils.makeAllValues( invP, c );

					if( log.isLoggable( Level.FINER ) )
						log.finer( "Absorb into " + ATermUtils.toString( ind )
								+ " with inverse of " + ATermUtils.toString( p ) + " for "
								+ ATermUtils.toString( c ) );

					absorbedAxioms.addAll( explanation );

					kb.addIndividual( ind );
					kb.addType( ind, allInvPC, new TimeDS( explanation ) );

					return true;
				}
			}

			return false;
		}
	}
	

	private class BinaryAbsorption implements Absorption {
		private boolean deterministic = false;
		
		BinaryAbsorption(boolean deterministic) {
			this.deterministic = deterministic;
		}
		
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			if( !PelletOptions.USE_BINARY_ABSORPTION )
				return false;
			
			if( deterministic && terms.size() > 3 )
				return false;
			
			Set<ATermAppl> candidates1  = CollectionUtils.makeIdentitySet();
			Set<ATermAppl> candidates2  = CollectionUtils.makeIdentitySet();
			for( ATermAppl term : terms ) {
				if( !isPrimitive( term ) )
					continue;
				if( !primitiveTbox.contains( term ) ) {
					candidates1.add( term );
					candidates2.add( term );
				}
				if( binaryTbox.contains( term ) ) {
					candidates1.add( term );
				}
			}
			
			if( candidates1.isEmpty() ) 
				return false;
			
			ATermAppl a1 = candidates1.iterator().next();
			candidates2.remove( a1 );
		
			if( candidates2.isEmpty() ) 
				return false;
		
			ATermAppl a2 = candidates2.iterator().next();
			
			BinarySet<ATermAppl> set = BinarySet.create( a1, a2 );
			Unfolding unfolding = binaryTbox.unfold( set );
			
			terms.remove( a1 );
			terms.remove( a2 );

			if( terms.size() == 0 ) {
				binaryTbox.add( set, BOTTOM, explanation );				
			}
			else if( terms.size() == 1 ) {
				binaryTbox.add( set, negate( terms.iterator().next() ), explanation );
			}
			else {
				ATermAppl a = null;
				if( unfolding == null ) {
					a = freshConcept(); 
					binaryTbox.add( set, a, explanation );
				}
				else {
					a = unfolding.getResult();
				}
				
				terms.add( a );
				
				absorbAxiom( terms, explanation );
			}
			
			return true;
		}
	}
	
	private class ExistentialAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			for( ATermAppl term : terms ) {
				if( !isSomeValues( term ) )
					continue;
				
				ATermAppl p = (ATermAppl) term.getArgument( 0 );
				ATermAppl c = (ATermAppl) term.getArgument( 1 );
				
				if( !kb.isObjectProperty( p ) )
					continue;
				
				terms.remove( term );
				
				if (terms.size() == 1 && isNegatedPrimitive(c)
						&& isNegatedPrimitive(terms.iterator().next())) {
					terms.add( term );
					return false;
				}
				
				ATermAppl a = freshConcept();
				terms.add( a );
				absorbAxiom( terms, explanation );
				
				Set<ATermAppl> newTerms = CollectionUtils.makeIdentitySet();
				newTerms.add( nnf( c ) );
				newTerms.add( some( inv( p ), not( a ) ) );
				absorbAxiom( newTerms, explanation );
				
				return true;
			}
			
			return false;
		}
	}
	
	private class UnfoldAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			for( ATermAppl c : terms ) {
				Unfolding unf = primitiveTbox.getDefinition( c );
				
				if( unf != null ) {
					ATermAppl def = unf.getResult();
					
					terms.remove( c );
					terms.add( nnf( def ) );
					
					absorbAxiom( terms, explanation );
					
					return true;
				}
			}
			
			return false;
		}
	}
	
	private abstract class AbstractUnaryAbsorption implements Absorption {
		protected boolean absorbIntoTerm(ATermAppl term, Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			if( isPrimitive( term ) && !primitiveTbox.contains( term ) ) {
				terms.remove( term );
				
				ATermAppl disjunction = disjunction( terms );
				unaryTbox.add( term, disjunction, explanation );

				return true;					
			}
			
			return false;
		}
	}
	
	private class DeterministicUnaryAbsorption extends AbstractUnaryAbsorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			if( terms.size() != 2 )
				return false;
			
			Iterator<ATermAppl> i = terms.iterator();

			ATermAppl first = i.next();
			if( absorbIntoTerm(first, terms, explanation) ) {
				return true;
			}
			
			ATermAppl second = i.next();
			if( absorbIntoTerm(second, terms, explanation) ) {
				return true;
			}
			
			return false;
		}
	}
	
	private class UnaryAbsorption extends AbstractUnaryAbsorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			for( ATermAppl term : terms ) {
				if( absorbIntoTerm(term, terms, explanation) ) {
					return true;
				}
			}
			
			return false;
		}
	}
		
	private class DomainAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {
			for( ATermAppl term : terms ) {
				if( !isSomeValues( term ) )
					continue;
				
				ATermAppl p = (ATermAppl) term.getArgument( 0 );
				
				Role role = kb.getRole( p );
				if( role == null || role.hasComplexSubRole() )
					continue;
				
				ATermAppl disjunction = disjunction( terms );
				kb.addDomain( p, disjunction, explanation );

				if( log.isLoggable( Level.FINE ) )
					log.fine( "Add dom: " + ATermUtils.toString( p ) + " " + ATermUtils.toString( disjunction ) );
				
				absorbedAxioms.addAll( explanation );
				return true;
			}
			
			return false;
		}
	}	
	
	private class GeneralAbsorption implements Absorption {
		public boolean absorb(Set<ATermAppl> terms, Set<ATermAppl> explanation) {			
			ATermAppl disjunction = disjunction( terms );
			unaryTbox.add( TOP, disjunction, explanation );
			return true;
		}
	}
	
	private int freshConceptCount = 0;
	private ATermAppl freshConcept() {
		return term( "_A" + (++freshConceptCount) + "_" );
	}
	
	public boolean removeAxiom(ATermAppl axiom) {
		return removeAxiom( axiom, axiom );
	}

	public boolean removeAxiom(ATermAppl dependantAxiom, ATermAppl explanationAxiom) {

		if( !PelletOptions.USE_TRACING ) {
			if( log.isLoggable( Level.FINE ) )
				log.fine( "Cannot remove axioms when PelletOptions.USE_TRACING is false" );
			return false;
		}

		if( absorbedAxioms.contains( dependantAxiom ) ) {
			if( log.isLoggable( Level.FINE ) )
				log.fine( "Cannot remove axioms that have been absorbed outside TBox" );
			return false;
		}

		tboxAssertedAxioms.remove( dependantAxiom );

		Set<ATermAppl> sideEffects = new HashSet<ATermAppl>();
		boolean removed = removeExplanation( dependantAxiom, explanationAxiom, sideEffects );

		// an axiom might be effectively removed as a side-effect of another
		// removal. For example see TBoxTests.removedByAbsorbReaddedOnChange
		for( ATermAppl readdAxiom : sideEffects ) {
			Set<Set<ATermAppl>> explanations = tboxAxioms.get( readdAxiom );
			// if the axiom is really removed (and not just side-effected)
			// then there wouldn't be any explanation and we shouldn't readd
			if( explanations != null ) {
				Iterator<Set<ATermAppl>> i = explanations.iterator();
				addAxiom( readdAxiom, i.next(), true );
				while( i.hasNext() )
					addAxiomExplanation( readdAxiom, i.next() );
			}
		}

		return removed;
	}

	private boolean removeExplanation(ATermAppl dependantAxiom, ATermAppl explanationAxiom,
			Set<ATermAppl> sideEffects) {
		boolean removed = false;

		if( !PelletOptions.USE_TRACING ) {
			if( log.isLoggable( Level.FINE ) )
				log.fine( "Cannot remove axioms when PelletOptions.USE_TRACING is false" );
			return false;
		}
		
		if( log.isLoggable( Level.FINE ) )
			log.fine( "Removing " + explanationAxiom );

		// this axiom is being removed so it cannot support any other axiom
		MultiMapUtils.remove( reverseExplain, explanationAxiom, dependantAxiom );

		Set<Set<ATermAppl>> explains = tboxAxioms.get( dependantAxiom );
		Set<Set<ATermAppl>> newExplains = new HashSet<Set<ATermAppl>>();

		if( explains != null ) {
			for( Set<ATermAppl> explain : explains ) {
				if( !explain.contains( explanationAxiom ) )
					newExplains.add( explain );
				else {
					sideEffects.addAll( explain );
					sideEffects.remove( explanationAxiom );
				}
			}
		}

		if( !newExplains.isEmpty() ) {
			// there are still other axioms supporting this axiom so it won't be
			// removed but we still need to update the explanations
			tboxAxioms.put( dependantAxiom, newExplains );

			// also make sure the concept on the left hand side is normalized
//			Tu.updateDef( dependantAxiom );

			// there is no need for a reload
			return true;
		}

		// there is no other explanation for this dependant axiom so
		// we can safely remove it
		removed |= (tboxAxioms.remove( dependantAxiom ) != null);

		AFun fun = dependantAxiom.getAFun();
		if( fun.equals( ATermUtils.SUBFUN ) || fun.equals( ATermUtils.EQCLASSFUN ) ) {
			// remove the axiom fom Tu and Tg
//			removed |= Tu.removeDef( dependantAxiom );
//			removed |= Tg.removeDef( dependantAxiom );
		}

		// find if this axiom supports any other axiom
		Set<ATermAppl> otherDependants = reverseExplain.remove( dependantAxiom );
		if( otherDependants != null ) {
			for( ATermAppl otherDependant : otherDependants ) {
				// remove this axiom from any explanation it contributes to

				if( otherDependant.equals( dependantAxiom ) )
					continue;

				removed |= removeExplanation( otherDependant, dependantAxiom, sideEffects );
			}
		}

		return removed;
	}

	public Collection<ATermAppl> getAxioms() {
		return tboxAxioms.keySet();
	}

	public Collection<ATermAppl> getAssertedAxioms() {
		return tboxAssertedAxioms;
	}

	public boolean containsAxiom(ATermAppl axiom) {
		return tboxAxioms.containsKey( axiom );
	}

	public void print() {
		try {
			print( System.out );
		} catch( IOException e ) {
			e.printStackTrace();
		}
	}

	public String toString() {
		StringBuilder sb = new StringBuilder();
		try {
			print( sb );
		} catch( IOException e ) {
			e.printStackTrace();
		}
		return sb.toString();
	}

	public void print(Appendable str) throws IOException {
//		generalTbox.print(str);
		primitiveTbox.print(str);
		unaryTbox.print(str);
		binaryTbox.print(str);
		str.append( "Explain: [\n" );
		for( ATermAppl axiom : tboxAxioms.keySet() ) {
			str.append( ATermUtils.toString( axiom ) );
			str.append( " -> " );
			str.append( tboxAxioms.get( axiom ).toString() );
			str.append( "\n" );
		}
		str.append( "]\nReverseExplain: [\n" );
		for( ATermAppl axiom : reverseExplain.keySet() ) {
			str.append( ATermUtils.toString( axiom ) );
			str.append( " -> " );
			str.append( reverseExplain.get( axiom ).toString() );
			str.append( "\n" );
		}
		str.append( "]\n" );
	}

	public boolean addClass(ATermAppl term) {
		boolean added = classes.add( term );

		if( added )
			allClasses = null;

		return added;
	}

	public Set<ATermAppl> getClasses() {
		return classes;
	}

	public Collection<ATermAppl> getAxioms(ATermAppl term) {
		List<ATermAppl> axioms = new ArrayList<ATermAppl>();
//		TermDefinition def = Tg.getTD( term );
//		if( def != null ) {
//			axioms.addAll( def.getSubClassAxioms() );
//			axioms.addAll( def.getEqClassAxioms() );
//		}
//		def = Tu.getTD( term );
//		if( def != null ) {
//			axioms.addAll( def.getSubClassAxioms() );
//			axioms.addAll( def.getEqClassAxioms() );
//		}

		return axioms;
	}

	public Iterator<Unfolding> unfold(ATermAppl c) {
		if( ATermUtils.isPrimitive( c ) ) {
			MultiIterator<Unfolding> result = 
				new MultiIterator<Unfolding>( primitiveTbox.unfold( c ) );
			result.append( unaryTbox.unfold( c ) );
			result.append( binaryTbox.unfold( c ) );
			return result;
		}
		else if( isNot( c ) ) {
			return primitiveTbox.unfold( c );
		}
		else {
			return IteratorUtils.emptyIterator();
		}
	}

	public boolean isPrimitive(ATermAppl c) {	
		return ATermUtils.isPrimitive( c ) && !primitiveTbox.contains( c );
	}

	public void prepare() {
		// nothing to do		
	}
}
