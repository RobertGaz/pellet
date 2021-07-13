// Portions Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// Clark & Parsia, LLC parts of this source code are available under the terms of the Affero General Public License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com
//
// ---
// Portions Copyright (c) 2003 Ron Alford, Mike Grove, Bijan Parsia, Evren Sirin
// Alford, Grove, Parsia, Sirin parts of this source code are available under the terms of the MIT License.
//
// The MIT License
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.

package org.mindswap.pellet.tableau.branch;

import java.util.List;

import org.mindswap.pellet.*;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;



public class MaxBranch extends IndividualBranch {
	private List<NodeMerge> mergePairs;
	private Role r;
	private int n;
	private ATermAppl qualification;
	private TimeDS[] prevDS;
	private Time time;

	public MaxBranch(ABox abox, CompletionStrategy strategy, Individual x, Role r, int n, ATermAppl qualification, List<NodeMerge> mergePairs, TimeDS maxDS) {
		super(abox, strategy, x, maxDS, mergePairs.size());
		
		this.r = r;
		this.n = n;
		this.mergePairs = mergePairs;
		this.qualification = qualification;
        this.prevDS = new TimeDS[mergePairs.size()];
        this.time = maxDS.time();
	}		
		
	public IndividualBranch copyTo(ABox abox) {
	    Individual x = abox.getIndividual(ind.getName());
	    MaxBranch b = new MaxBranch(abox, null, x, r, n, qualification, mergePairs, getTermDepends());
	    b.setAnonCount( getAnonCount() );
	    b.setNodeCount( nodeCount );
	    b.setBranch( branch );
	    b.setStrategy( strategy );
        b.setTryNext( tryNext );
        b.prevDS = new TimeDS[prevDS.length];
        System.arraycopy(prevDS, 0, b.prevDS, 0, getTryNext() );
        
	    return b;
	}
	
	protected void tryBranch() {		
		abox.incrementBranch();

		TimeDS timeDS = getTermDepends().copy();
		for(; getTryNext() < getTryCount(); tryNext++) {		
			this.abox.getKB().timers.mainTimer.check();
			if(PelletOptions.USE_SEMANTIC_BRANCHING) {
				for(int m = 0; m < getTryNext(); m++) {
					NodeMerge nm = mergePairs.get(m);			
					Node y = abox.getNode(nm.getSource()).getSame();
					Node z = abox.getNode(nm.getTarget()).getSame();
					strategy.setDifferent(y, z, prevDS[m]);
				}
			}
			
			NodeMerge nm = mergePairs.get(getTryNext());			
			Node y = abox.getNode(nm.getSource()).getSame();
			Node z = abox.getNode(nm.getTarget()).getSame();

			log.info("MAX   Branch(" + getBranch() + "), try(" + (getTryNext() + 1) + "/" + mergePairs.size() + "). " +
						ind + " -> " + r + " -> " + ATermUtils.toString(qualification) + " > " + n +
						". Now will merge " + y + " to " + z + " " + timeDS);

//			КОРОЧЕ ТУТ ДОБАВЛЯЕМ ВЕТКУ НО все DS в мапе в TimeDS должны быть именно скопированы - поэтоиу не подойдет add(getBranch())
			timeDS.unite(new DependencySet(getBranch()), abox.doExplanation());
			
			// max cardinality merge also depends on all the edges 
			// between the individual that has the cardinality and 
			// nodes that are going to be merged 
			EdgeList rNeighbors = ind.getRNeighborEdges(r);
			boolean yEdge = false, zEdge = false;
			for( Edge edge : rNeighbors ) {
				Node neighbor = edge.getNeighbor( ind );
				
				if( neighbor.equals( y ) ) {
					timeDS = TimeDS.intersection(timeDS, edge.getDepends(), abox.doExplanation() );
					yEdge = true;
				}
				else if( neighbor.equals( z ) ) {
					timeDS = TimeDS.intersection(timeDS, edge.getDepends(), abox.doExplanation() );
					zEdge = true;
				}
			}
			
			// if there is no edge coming into the node that is
			// going to be merged then it is not possible that
			// they are affected by the cardinality restriction
			// just die instead of possibly unsound results
			if(!yEdge || !zEdge)
			    throw new InternalReasonerException( 
			        "An error occurred related to the max cardinality restriction about "  + r);
			
			// if the neighbor nodes did not have the qualification
			// in their type list they would have not been affected
			// by the cardinality restriction. so this merges depends
			// on their types
			timeDS = TimeDS.intersection( timeDS, y.getDepends(qualification), abox.doExplanation() );
			timeDS = TimeDS.intersection( timeDS, z.getDepends(qualification), abox.doExplanation() );
			
            // if there were other merges based on the exact same cardinality
			// restriction then this merge depends on them, too (we wouldn't
			// have to merge these two nodes if the previous merge did not
			// eliminate some other possibilities)
	        for( int b = abox.getBranches().size() -2; b >=0; b-- ) {
	        	Branch branch = abox.getBranches().get( b );
	        	if( branch instanceof MaxBranch ) {
	        		MaxBranch prevBranch = (MaxBranch) branch;
	        		if( prevBranch.ind.equals( ind )
	        			&& prevBranch.r.equals( r )
	        			&& prevBranch.qualification.equals( qualification )
						&& prevBranch.time.equals(time)) {
	        			timeDS.add( prevBranch.getBranch() );
	        		} else {
	        			break;
	        		}
	        	}
	        	else
	        		break;
	        }

	        if (!timeDS.time().equals(getTermDepends().time()) || timeDS.size() != 1) {
	        	throw new RuntimeException("Ne tak ved' zadumano bylo!");
			}

			strategy.mergeTo(y, z, timeDS);

//			abox.validate();

			boolean earlyClash = abox.isClosed();
			if(earlyClash) {
				log.info("CLASH  Branch " + getBranch() + " " + abox.getClash() + "!");

				TimeDS clashDS = abox.getClash().getDepends();

				timeDS = timeDS.copy();

				if(clashDS.contains(getBranch())) {
					TimeDS clashDS_copy = clashDS.copy();
					// we need a global restore here because the merge operation modified three
					// different nodes and possibly other global variables

//					ROBERT мб тут надо restore на всей временной прямой??
					strategy.restore(this, clashDS.time());
					
					// global restore sets the branch number to previous value so we need to
					// increment it again
					abox.incrementBranch();
									
                    setLastClash( clashDS_copy );
				}
				else
					return;
			} 
			else 
				return;	
		}
		
        timeDS = getCombinedClash();
        
        timeDS.remove( getBranch() );
        
		if(abox.doExplanation())
		    abox.setClash(Clash.maxCardinality(ind, timeDS, r.getName(), n));
		else
		    abox.setClash(Clash.maxCardinality(ind, timeDS));
	}
	
    public void setLastClash( TimeDS timeDS ) {
		timeDS = timeDS.copy();
        super.setLastClash( timeDS );
        if(getTryNext()>=0)
        	prevDS[getTryNext()] = timeDS;
    }
	
	public String toString() {
		if(getTryNext() < mergePairs.size())
			return "Branch " + getBranch() + " max rule on " + ind + " merged  " + mergePairs.get(getTryNext());
		
		return "Branch " + getBranch() + " max rule on " + ind + " exhausted merge possibilities";
	}
	
}