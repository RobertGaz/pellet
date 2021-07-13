// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public
// License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of
// proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion.rule;

import java.util.List;
import org.mindswap.pellet.Clash;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.TimeDS;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;

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
public class NominalRule extends AbstractTableauRule {

	public NominalRule(CompletionStrategy strategy) {
		super( strategy, BlockingType.NONE );
	}

	public void apply(Individual y) {
		List<ATermAppl> types = y.getTypes( Node.NOM );
		for (ATermAppl nc : types) {
			TimeDS timeDS = y.getDepends(nc);

			if (timeDS == null || timeDS.isEmpty())
				continue;

			applyNominalRule(y, nc, timeDS);

			if (strategy.getABox().isClosed())
				return;

			if (y.isMerged()) {
				apply(y.getSame());
				return;
			}
		}
	}

	void applyNominalRule(Individual y, ATermAppl nc, TimeDS timeDS) {
		strategy.getABox().copyOnWrite();

		ATermAppl nominal = (ATermAppl) nc.getArgument( 0 );
		// first find the individual for the given nominal
		Individual z = strategy.getABox().getIndividual( nominal );
		if( z == null ) {
			if( ATermUtils.isAnonNominal( nominal ) ) {
				z = strategy.getABox().addIndividual( nominal, timeDS );
			}
			else
				throw new InternalReasonerException( "Nominal " + nominal + " not found in KB!" );
		}

		// Get the value of mergedTo because of the following possibility:
		// Suppose there are three individuals like this
		// [x,{}],[y,{value(x)}],[z,{value(y)}]
		// After we merge x to y, the individual x is now represented by
		// the node y. It is too hard to update all the references of
		// value(x) so here we find the actual representative node
		// by calling getSame()
		if( z.isMerged() ) {
			timeDS = timeDS.union( z.getMergeDependency( true ), strategy.getABox().doExplanation() );

			z = z.getSame();
		}

		if( y.isSame( z ) )
			return;

		if( y.isDifferent( z ) ) {
			timeDS.unite( y.getDifferenceDependency( z ).ds(), strategy.getABox().doExplanation() );
			if( strategy.getABox().doExplanation() )
				strategy.getABox().setClash( Clash.nominal( y, timeDS, z.getName() ) );
			else
				strategy.getABox().setClash( Clash.nominal( y, timeDS ) );
			return;
		}

		log.info( "NOM   " + y + " -> " + z );

		strategy.mergeTo( y, z, timeDS );
	}
}
