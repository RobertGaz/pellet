// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion.rule;

import java.util.Iterator;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

import org.mindswap.pellet.*;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;

/**
 * <p>
 * Title:
 * </p>
 * <p>
 * Description:
 * </p>
 * <p>
 * Copyright: Copyright (c) 2009
 * </p>
 * <p>
 * Company: Clark & Parsia, LLC. <http://www.clarkparsia.com>
 * </p>
 * 
 * @author Evren Sirin
 */
public class AllValuesRule extends AbstractTableauRule {
	public AllValuesRule(CompletionStrategy strategy) {
		super( strategy, BlockingType.NONE );
	}

    public void apply( Individual x ) {
	    List<ATermAppl> allValues = x.getTypes( Node.ALL );
        int size = allValues.size();
        Iterator<ATermAppl> i = allValues.iterator();
        while( i.hasNext() ) {
            ATermAppl av = i.next();
            TimeDS avDepends = x.getDepends( av );

            if(avDepends.isEmpty())
                throw new RuntimeException("strange");
            
            applyAllValues( x, av, avDepends );

            if( x.isMerged() || strategy.getABox().isClosed() )
                return;

            // if there are self links through transitive properties restart
            if( size != allValues.size() ) {
                i = allValues.iterator();
                size = allValues.size();
            }
        }
    }

    
    /**
     * Apply the allValues rule for the given type with the given dependency. The concept is in the
     * form all(r,C) and this function adds C to all r-neighbors of x
     * 
     * @param x
     * @param av
     * @param timeDS
     */
    public void applyAllValues( Individual x, ATermAppl av, TimeDS timeDS ) {
        // Timer timer = kb.timers.startTimer("applyAllValues");

        if( av.getArity() == 0 )
            throw new InternalReasonerException();
        ATerm p = av.getArgument( 0 );
        ATermAppl c = (ATermAppl) av.getArgument( 1 );

        ATermList roleChain = ATermUtils.EMPTY_LIST;
        Role s = null;
        if( p.getType() == ATerm.LIST ) {
            roleChain = (ATermList) p;
            s = strategy.getABox().getRole( roleChain.getFirst() );
            roleChain = roleChain.getNext();
        }
        else
            s = strategy.getABox().getRole( p );

        if ( s.isTop() && s.isObjectRole() ) {
        	applyAllValuesTop( av, c, timeDS );
        	return;
        }

        EdgeList edges = x.getRNeighborEdges( s );
        for( int e = 0; e < edges.size(); e++ ) {
            Edge edgeToY = edges.edgeAt( e );
            Node y = edgeToY.getNeighbor( x );
            TimeDS finalDS = TimeDS.intersection(timeDS, edgeToY.getDepends(), strategy.getABox().doExplanation());
            if (!finalDS.isEmpty()) {
                if( roleChain.isEmpty() )
                    applyAllValues( x, s, y, c, finalDS );
                else if(y.isIndividual()) {
                    ATermAppl allRC = ATermUtils.makeAllValues(roleChain, c);
                    strategy.addType(y, allRC, finalDS);
                }

                if( x.isMerged() || strategy.getABox().isClosed() )
                    return;
            }

        }

        if( !s.isSimple() ) {
            Set<ATermList> subRoleChains = s.getSubRoleChains();
            for( Iterator<ATermList> it = subRoleChains.iterator(); it.hasNext(); ) {
                ATermList chain = it.next();
                timeDS = timeDS.copy();
                timeDS.addExplain(s.getExplainSub(chain), strategy.getABox().doExplanation() );
				if (!applyAllValuesPropertyChain(x, chain, c, av, timeDS))
					return;
            }
        }
        
        if (!roleChain.isEmpty()) {
        	applyAllValuesPropertyChain(x, (ATermList) p, c, av, timeDS);
        }

        // timer.stop();
    }

//    ROBERT POCHEMU TIMEDS NOT USED??
    protected boolean applyAllValuesPropertyChain(Individual x, ATermList chain, ATermAppl c, ATermAppl xType, TimeDS timeDS ) {
         Role r = strategy.getABox().getRole( chain.getFirst() );
         
         EdgeList edges = x.getRNeighborEdges( r );
         if( !edges.isEmpty() ) {
             ATermAppl allRC = ATermUtils.makeAllValues( chain.getNext(), c );

             TimeDS typeDS = x.getDepends(xType);

             for( int e = 0; e < edges.size(); e++ ) {
                 Edge edgeToY = edges.edgeAt( e );
                 Node y = edgeToY.getNeighbor( x );
                 TimeDS finalDS = TimeDS.intersection(edgeToY.getDepends(), typeDS, strategy.getABox().doExplanation());
                 if (!finalDS.isEmpty()) {
                     applyAllValues( x, r, y, allRC, finalDS );
                     if( x.isMerged() || strategy.getABox().isClosed() )
                         return false;
                 }
             }
         }
         
         return true;
    }


//    DONE
    protected void applyAllValues(Individual subj, Role pred, Node obj, ATermAppl c, TimeDS timeDS ) {
        if (subj.toString().equals("SangioveseGrape")&&pred.toString().equals("inv(madeFromGrape)")&&obj.toString().equals("WhitehallLanePrimavera")) {
            System.out.println("zhukk");
        }
        if( !obj.hasType( c ) ) {
            log.info( "ALL   " + subj + " -> " + pred + " -> " + obj + " : " + ATermUtils.toString( c ) + (!PelletOptions.SPECIAL_LOGS ? " ON " + timeDS.time() : "") );

            strategy.addType( obj, c, timeDS );
        }
    }
    

    public void applyAllValues( Individual subj, Role pred, Node obj, TimeDS edgeDS ) {
        List<ATermAppl> allValues = subj.getTypes( Node.ALL );
        int allValuesSize = allValues.size();
        Iterator<ATermAppl> i = allValues.iterator();
        while( i.hasNext() ) {
            ATermAppl av = i.next();

            ATerm p = av.getArgument( 0 );
            ATermAppl c = (ATermAppl) av.getArgument( 1 );
            
            ATermList roleChain = ATermUtils.EMPTY_LIST;
            Role s = null;
            if( p.getType() == ATerm.LIST ) {
                roleChain = (ATermList) p;
                s = strategy.getABox().getRole( roleChain.getFirst() );
                roleChain = roleChain.getNext();
            }
            else
                s = strategy.getABox().getRole( p );
                        
            if ( s.isTop() && s.isObjectRole() ) {
            	applyAllValuesTop( av, c, edgeDS );
            	if( strategy.getABox().isClosed() )
                    return;
            	continue;
            }

            if( pred.isSubRoleOf( s ) ) {
                TimeDS typeDS = subj.getDepends(av);
                TimeDS finalDS = TimeDS.intersection(edgeDS, typeDS, strategy.getABox().doExplanation());
                if (!finalDS.isEmpty()) {
                    finalDS.addExplain(s.getExplainSubOrInv( pred ), strategy.getABox().doExplanation());
                    if( roleChain.isEmpty() )
                        applyAllValues( subj, s, obj, c, finalDS );
                    else if (obj.isIndividual()) {
                        ATermAppl allRC = ATermUtils.makeAllValues( roleChain, c );
                        strategy.addType( obj, allRC, finalDS );
                    }
                    if( strategy.getABox().isClosed() )
                        return;
                }
            }

            if( !s.isSimple() ) {
                TimeDS finalDS = TimeDS.intersection(edgeDS, subj.getDepends(av), strategy.getABox().doExplanation());
                if (!finalDS.isEmpty()){
                    finalDS.addExplain(s.getExplainSubOrInv( pred ), strategy.getABox().doExplanation());

                    Set<ATermList> subRoleChains = s.getSubRoleChains();
                    for( Iterator<ATermList> it = subRoleChains.iterator(); it.hasNext(); ) {
                        ATermList chain = it.next();

                        Role firstRole = strategy.getABox().getRole(chain.getFirst());
                        if (!pred.isSubRoleOf(firstRole))
                            continue;

                        ATermAppl allRC = ATermUtils.makeAllValues(chain.getNext(), c);

                        finalDS.addExplain(firstRole.getExplainSub(pred.getName()), strategy.getABox().doExplanation());
                        finalDS.addExplain(s.getExplainSub(chain), strategy.getABox().doExplanation());
                        applyAllValues(subj, pred, obj, allRC, finalDS);

                        if (subj.isMerged() || strategy.getABox().isClosed())
                            return;
                    }
                }
            }

            if( subj.isMerged() )
                return;

            obj = obj.getSame();

            // if there are self links then restart
            if( allValuesSize != allValues.size() ) {
                i = allValues.iterator();
                allValuesSize = allValues.size();
            }
        }
    }
    
    /**
     * Apply all values restriction for the Top object role
     */
    void applyAllValuesTop( ATermAppl allTopC, ATermAppl c, TimeDS timeDS ) {
		for( Node node : strategy.getABox().getNodes() ) {
			if( node.isIndividual() && !node.isPruned() && !node.hasType( c ) ) {
				node.addType( c, timeDS );
				node.addType( allTopC, timeDS );
				
				if( strategy.getABox().isClosed() )
					break;
			}
		}
		
    }
}
