// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion.rule;

import java.util.List;
import java.util.logging.Level;

import org.mindswap.pellet.*;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;
import aterm.ATermInt;

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
public class MinRule extends AbstractTableauRule {
	public MinRule(CompletionStrategy strategy) {
		super( strategy, BlockingType.COMPLETE );
	}

    public void apply( Individual x ) {
        if( !x.canApply( Node.MIN ) )
        	return;

        // We get all the minCard restrictions in the node and store
        // them in the list ''types''
        List<ATermAppl> types = x.getTypes( Node.MIN );
        int size = types.size();
        for( int j = x.applyNext[Node.MIN]; j < size; j++ ) {
            // mc stores the current type (the current minCard restriction)
            ATermAppl mc = types.get( j );

            apply( x, mc );

            if( strategy.getABox().isClosed() )
                return;
        }
        x.applyNext[Node.MIN] = size;
    }
    
    protected void apply( Individual x, ATermAppl mc ) {
        // We retrieve the role associated to the current
        // min restriction
        Role r = strategy.getABox().getRole( mc.getArgument( 0 ) );
        int n = ((ATermInt) mc.getArgument( 1 )).getInt();
        ATermAppl c = (ATermAppl) mc.getArgument( 2 );


        TimeDS timeDS = x.getDepends( mc );
        
        if(timeDS.isEmpty())
            throw new RuntimeException("strange");


        // FIXME make sure all neighbors are safe
        if( x.hasDistinctRNeighborsForMin( r, n, c, false ) )
            return;

        TimeDS ds = x.getDepends( mc );

        if(ds.isEmpty())
            throw new RuntimeException("strange");

            log.info( "MIN   " + x + " -> " + r + " -> anon"
                + (n == 1 ? "" : (strategy.getABox().getAnonCount() + 1) + " - anon") + (strategy.getABox().getAnonCount() + n) + " "
                + ATermUtils.toString( c ) + " " +" ON " + timeDS );

        Node[] y = new Node[n];
        for( int c1 = 0; c1 < n; c1++ ) {
        	strategy.checkTimer();
            if( r.isDatatypeRole() )
                y[c1] = strategy.getABox().addLiteral( timeDS );
            else {
                y[c1] = strategy.createFreshIndividual( x, timeDS );
            }
            Node succ = y[c1];
            TimeDS finalDS = timeDS;

            strategy.addEdge( x, r, succ, timeDS );
            if( succ.isPruned() ) {
                finalDS = finalDS.union( succ.getMergeDependency( true ), strategy.getABox().doExplanation() );
                succ = succ.getMergedTo();
            }

            strategy.addType( succ, c, finalDS );
            for( int c2 = 0; c2 < c1; c2++ )
                succ.setDifferent( y[c2], finalDS );
        }
    }
}
