// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion.rule;

import java.util.Iterator;
import java.util.List;

import org.mindswap.pellet.*;
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
public class SimpleAllValuesRule extends AllValuesRule {
	public SimpleAllValuesRule(CompletionStrategy strategy) {
		super( strategy);
	}
	

    @Override
	public void applyAllValues(Individual x, ATermAppl av, TimeDS timeDS) {
    	ATermAppl p = (ATermAppl) av.getArgument( 0 );
		ATermAppl c = (ATermAppl) av.getArgument( 1 );
		
		Role s = strategy.getABox().getRole( p );
		
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
				if (strategy.getABox().doExplanation()) {
					Role edgeRole = edgeToY.getRole();
					finalDS.addExplain(s.getExplainSubOrInv(edgeRole), true);
				}

				applyAllValues(x, s, y, c, finalDS);

				if (x.isMerged())
					return;
			}
		}

		if( !s.isSimple() ) {
			for( Role r : s.getTransitiveSubRoles() ) {
				ATermAppl allRC = ATermUtils.makeAllValues( r.getName(), c );

				edges = x.getRNeighborEdges( r );
				for( int e = 0; e < edges.size(); e++ ) {
					Edge edgeToY = edges.edgeAt( e );
					Node y = edgeToY.getNeighbor( x );
					TimeDS finalDS = TimeDS.intersection(timeDS, edgeToY.getDepends(), strategy.getABox().doExplanation());
					if (!finalDS.isEmpty()) {
						if (strategy.getABox().doExplanation()) {
							finalDS.addExplain(r.getExplainTransitive(), true);
							finalDS.addExplain(s.getExplainSubOrInv(edgeToY.getRole()), true);
						}
						applyAllValues(x, r, y, allRC, finalDS);

						if (x.isMerged())
							return;
					}
				}
			}
		}
	}

    @Override
	public void applyAllValues( Individual subj, Role pred, Node obj, TimeDS edgeDS) {
		List<ATermAppl> allValues = subj.getTypes( Node.ALL );
		int size = allValues.size();
		Iterator<ATermAppl> i = allValues.iterator();
		while( i.hasNext() ) {
			ATermAppl av = i.next();
			ATermAppl p = (ATermAppl) av.getArgument( 0 );
			ATermAppl c = (ATermAppl) av.getArgument( 1 );			
			
			Role s = strategy.getABox().getRole( p );
			
			if ( s.isTop() && s.isObjectRole() ) {
            	applyAllValuesTop( av, c, edgeDS );
            	continue;
            }


			if( pred.isSubRoleOf( s ) ) {
				TimeDS typeDS = subj.getDepends(av);
				TimeDS finalDS = TimeDS.intersection(edgeDS, typeDS, strategy.getABox().doExplanation());
				if (!finalDS.isEmpty()) {
					if (strategy.getABox().doExplanation())
						finalDS.addExplain(s.getExplainSubOrInv(pred), true);

					applyAllValues(subj, s, obj, c, finalDS);
				}

				if( s.isTransitive() ) {
					ATermAppl allRC = ATermUtils.makeAllValues(s.getName(), c);
					finalDS = TimeDS.intersection(typeDS, edgeDS, strategy.getABox().doExplanation());
					if (!finalDS.isEmpty()) {
						if (strategy.getABox().doExplanation())
							finalDS.addExplain(s.getExplainTransitive(), true);
						applyAllValues(subj, s, obj, allRC, finalDS);
					}
				}
			}

			// if there are self links through transitive properties restart
			if( size != allValues.size() ) {
				i = allValues.iterator();
				size = allValues.size();
			}
		}
	}


}
