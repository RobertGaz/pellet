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

import java.util.Arrays;
import java.util.logging.Level;


import org.mindswap.pellet.*;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.ATermUtils;

import aterm.ATermAppl;


public class DisjunctionBranch extends Branch {
	protected Node node;
	protected ATermAppl disjunction;
	private ATermAppl[] disj;
	protected TimeDS[] prevDS;
	protected int[] order;

	protected Time[] tryNextTime;
	
	public DisjunctionBranch(ABox abox, CompletionStrategy completion, Node node, ATermAppl disjunction, TimeDS timeDS, ATermAppl[] disj) {
		super(abox, completion, timeDS, disj.length);
		
		this.node = node;
		this.disjunction = disjunction;
		this.setDisj( disj );
        this.prevDS = new TimeDS[disj.length];
		this.order = new int[disj.length];
        for(int i = 0; i < disj.length; i++)
            order[i] = i;

		tryNextTime = new Time[getTryCount()];
		tryNextTime[0] = timeDS.time();
	}
	
	public Node getNode() {
		return node;
	}

    protected String getDebugMsg() {
        return "DISJ  Branch(" + getBranch() + "), try(" + (getTryNext() + 1) + "/" + getTryCount()
            + "). " + node + ":" + ATermUtils.toString(disjunction) + (!PelletOptions.SPECIAL_LOGS ? " ON " + getTryNextTime() : "");
    }
	
	public DisjunctionBranch copyTo(ABox abox) {
	    Node n = abox.getNode(node.getName());
	    DisjunctionBranch b = new DisjunctionBranch(abox, null, n, disjunction, getTermDepends(), disj);
	    b.setAnonCount( anonCount );
	    b.setNodeCount( nodeCount );
	    b.setBranch( branch );
	    b.setStrategy( strategy );
        b.tryNextTime = this.tryNextTime;

        b.prevDS = new TimeDS[disj.length];
        System.arraycopy(prevDS, 0, b.prevDS, 0, disj.length );
        b.order = new int[disj.length];
        System.arraycopy(order, 0, b.order, 0, disj.length );

	    return b;
	}
	
	/**
	 * This function finds preferred disjuncts using different heuristics.
	 * 
	 * 1) A common kind of axiom that exist in a lot of  ontologies is 
	 * in the form A = and(B, some(p, C)) which is absorbed into an
	 * axiom like sub(B, or(A, all(p, not(C))). For these disjunctions,
	 * we always prefer picking all(p, C) because it causes an immediate 
	 * clash for the instances of A so there is no overhead. For 
	 * non-instances of A, this builds better pseudo models     
     * 
	 * @return
	 */
	private int preferredDisjunct() {
        if( disj.length != 2 ) 
            return -1;
        
        if( ATermUtils.isPrimitive( disj[0] ) && 
            ATermUtils.isAllValues( disj[1] ) &&
            ATermUtils.isNot( (ATermAppl) disj[1].getArgument( 1 ) ) )
            return 1;
            	                
        if( ATermUtils.isPrimitive( disj[1] ) && 
            ATermUtils.isAllValues( disj[0] ) &&
            ATermUtils.isNot( (ATermAppl) disj[0].getArgument( 1 ) ) )
            return 0;
        
        return -1;
	}

	public void 	setLastClash( TimeDS clashDS ) {
		super.setLastClash(clashDS);
		tryNextTime[getTryNext()].subtract(clashDS.time());
		if (getTryNext() + 1 != getTryCount()) {
			tryNextTime[getTryNext() + 1] = clashDS.time();
		}
		prevDS[getTryNext()] = clashDS.copy();
	}

	protected void tryBranch() {			
		abox.incrementBranch();

		int[] stats = null;
		
		Node node = this.node.getSame();

		for(; getTryNext() < getTryCount(); tryNext++) {
			ATermAppl d = disj[getTryNext()];
			Time time = getTryNextTime();
			if (time == null || time.isEmpty()) {
				break;
			}

			if(PelletOptions.USE_SEMANTIC_BRANCHING) {
				for(int m = 0; m < getTryNext(); m++)
					strategy.addType(node, ATermUtils.negate(disj[m]), prevDS[m].partBy(time));
			}

			TimeDS timeDS = null;
			if (getTryNext() == getTryCount() - 1 && !PelletOptions.SATURATE_TABLEAU) {
				timeDS = getTermDepends();
				for(int m = 0; m < getTryNext(); m++)
//					ROBERT тут не intersection?
					timeDS = TimeDS.union(timeDS, prevDS[m], abox.doExplanation());
				timeDS = timeDS.partBy(time);
				timeDS.remove(branch);
			} else {
				timeDS = new TimeDS(time, new DependencySet(branch));
			}

			log.info(getDebugMsg() );

			ATermAppl notD = ATermUtils.negate(d);
			TimeDS clashDS = PelletOptions.SATURATE_TABLEAU ?
					TimeDS.empty():
					TimeDS.clash(node.getDepends(notD), timeDS, abox.doExplanation());

			if (node.toString().equals("Minnie")) {
				System.out.println("SOUT");
			}

			if (clashDS.isEmpty()) {
				strategy.addType(node, d, timeDS);
				// we may still find a clash if concept is allValuesFrom
				// and there are some conflicting edges
				if(abox.isClosed())
					clashDS = abox.getClash().getDepends();
			}

			if(clashDS.isEmpty()) {
				return;
			}

			// if there is a clash
			if( log.isLoggable( Level.INFO ) ) {
				Clash clash = abox.isClosed() ? abox.getClash() : Clash.atomic(node, clashDS, d);
				log.info("CLASH Branch " + getBranch() + " " + clash + "!" + " " + clashDS.getExplain());
			}

			if (!Time.subtraction(clashDS.time(), time).isEmpty()) {
				throw new RuntimeException("check need check TIME");
			}

			// do not restore if we do not have any more branches to try. after
			// backtrack the correct branch will restore it anyway. more
			// importantly restore clears the clash info causing exceptions
			if (getTryNext() < getTryCount() - 1 && clashDS.contains(branch)) {
				// do not restore if we find the problem without adding the concepts
				if(abox.isClosed()) {
					if( node.isLiteral() ) {
						abox.setClash( null );
						node.restore( branch, clashDS.time() );
					} else {
						// restoring a single node is not enough here because one of the disjuncts could be an
						// all(r,C) that changed the r-neighbors
						strategy.restoreLocal((Individual) node, this, clashDS.time());

						// global restore sets the branch number to previous value so we need to
						// increment it again
						abox.incrementBranch();
					}
				}
				setLastClash( clashDS );

			} else {

				// set the clash only if we are returning from the function
				if(abox.doExplanation()) {
					ATermAppl positive = (ATermUtils.isNot(notD) ? d : notD);
					abox.setClash(Clash.atomic(node, clashDS, positive));
				} else {
					abox.setClash(Clash.atomic(node, clashDS));
				}

				tryNextTime[getTryNext()].subtract(clashDS.time());

//				if (isUselessBranch() && branch > 1) {
//					log.info("I am useless Branch DISJ (" +branch+") -> deleting branches "+branch + "..." + abox.getBranches().size() +"  from ABox.");
//					abox.getBranches().subList(branch-1, abox.getBranches().size()).clear();
//				}

				return;
			}
		}
	}

	/**
	 * @param disj the disj to set
	 */
	public void setDisj(ATermAppl[] disj) {
		this.disj = disj;
	}

	/**
	 * @return the disj
	 */
	public ATermAppl getDisjunct(int i) {
		return disj[i];
	}


	public Time getTryNextTime() {
		return tryNextTime[getTryNext()];
	}

	public boolean isUselessBranch() {
		return Arrays.stream(tryNextTime).allMatch(t -> t.isEmpty());
	}

	public boolean currentlyUseless() {
		for (int i = 0; i < getTryNext(); ++i) {
			if (!tryNextTime[i].isEmpty()) {
				return false;
			}
		}
		return true;
	}


}