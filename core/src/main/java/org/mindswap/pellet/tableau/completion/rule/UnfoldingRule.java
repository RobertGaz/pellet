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
import java.util.logging.Logger;

import org.mindswap.pellet.*;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.tbox.impl.Unfolding;
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
public class UnfoldingRule extends AbstractTableauRule {
    public final static Logger log = Logger.getLogger( UnfoldingRule.class.getName() );

	public UnfoldingRule(CompletionStrategy strategy) {
		super( strategy, BlockingType.COMPLETE );
	}
    
    public void apply( Individual node ) {
        if( !node.canApply( Node.ATOM ) )
        	return;
        
        List<ATermAppl> types = node.getTypes( Node.ATOM );
        int size = types.size();
        for( int j = node.applyNext[Node.ATOM]; j < size; j++ ) {
            ATermAppl c = types.get( j );

            if(node.getDepends(c).isEmpty())
                throw new RuntimeException("strange");
            
            applyUnfoldingRule( node, c );
            
            if( strategy.getABox().isClosed() )
                return; 
            
            // it is possible that unfolding added new atomic 
            // concepts that we need to further unfold
            size = types.size();  
        }
        node.applyNext[Node.ATOM] = size;
    }
    
    protected void applyUnfoldingRule( Individual node, ATermAppl c ) {
    	TimeDS ds = node.getDepends( c );
        
        if(ds.isEmpty())
            throw new RuntimeException("strange");
        
        Iterator<Unfolding> unfoldingList = strategy.getTBox().unfold( c );

        while( unfoldingList.hasNext() ) {
			Unfolding unfolding = unfoldingList.next();
        	ATermAppl unfoldingCondition = unfolding.getCondition();
        	TimeDS finalDS = node.getDepends( unfoldingCondition );
        	
        	if( finalDS == null )
        		continue;

			finalDS = TimeDS.intersection(finalDS, ds, strategy.getABox().doExplanation());
			if (!finalDS.isEmpty()) {
                Set<ATermAppl> unfoldingDS = unfolding.getExplanation();
                finalDS.addExplain(new DependencySet(unfoldingDS), strategy.getABox().doExplanation());

                ATermAppl unfoldedConcept = unfolding.getResult();
                finalDS.subtract(node.getDepends(unfoldedConcept).time());

                if (!finalDS.isEmpty()) {
                    log.info("UNF   " + node + " : " + ATermUtils.toString(c) + " -> " + ATermUtils.toString(unfoldedConcept) + " ON " + finalDS);
                    strategy.skipNextAddLog();
                }

                strategy.addType(node, unfoldedConcept, finalDS);
            }
        }
    }
}
