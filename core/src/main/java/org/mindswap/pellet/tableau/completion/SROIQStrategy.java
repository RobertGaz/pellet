// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public
// License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of
// proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion;

import java.util.List;
import java.util.logging.Level;

import org.mindswap.pellet.ABox;
import org.mindswap.pellet.IndividualIterator;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.Time;
import org.mindswap.pellet.TimeDS;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.tableau.branch.Branch;
import org.mindswap.pellet.tableau.branch.DisjunctionBranch;
import org.mindswap.pellet.tableau.branch.IndividualBranch;
import org.mindswap.pellet.tableau.branch.MaxBranch;
import org.mindswap.pellet.tableau.completion.rule.TableauRule;

import com.clarkparsia.pellet.expressivity.Expressivity;

/**
 * <p>
 * Title:
 * </p>
 * <p>
 * Description:
 * </p>
 * <p>
 * Copyright: Copyright (c) 2006
 * </p>
 * <p>
 * Company: Clark & Parsia, LLC. <http://www.clarkparsia.com>
 * </p>
 * 
 * @author Evren Sirin
 */
public class SROIQStrategy extends CompletionStrategy {
	private boolean branchDeleted = false;
	public SROIQStrategy(ABox abox) {
		super( abox );
	}

	protected boolean backtrack() {
		boolean branchFound = false;
		abox.stats.backtracks++;
		List<Branch> branches = abox.getBranches();
		while (!branchFound) {
			completionTimer.check();
			for (int br : abox.getClash().getDepends().maxBranches()) {
				// no more branches to try
				if (br <= 0)
					return false;
				if (br > branches.size())
					throw new InternalReasonerException("Backtrack: Trying to backtrack to branch "
							+ br + " but has only " + branches.size()
							+ " branches. Clash found: " + abox.getClash());

				Branch branch = branches.get(br - 1);

				if (br != branch.getBranch())
					throw new InternalReasonerException("Backtrack: Trying to backtrack to branch " + br + " but got " + branch.getBranch());

			}

			int targetBranch = abox.getClash().getDepends().max();

			Branch branchVar = branches.get(targetBranch - 1);

			TimeDS clashDS = abox.getClash().getDepends().partByMax(targetBranch);


			if (branchVar instanceof IndividualBranch) {
				IndividualBranch branch = (IndividualBranch) branchVar;

				abox.stats.backjumps += (branches.size() - targetBranch);
				if (!PelletOptions.SPECIAL_LOGS) {
					log.info("(SROIQ) soon will restore max Branch(" + targetBranch + "). Deleting later branches " + Integer.sum(targetBranch, 1) + "..." + abox.getBranches().size() + "  from ABox.");
				} else {
					log.info("(SROIQ) soon will restore Branch(" + targetBranch + "). Deleting later branches " + Integer.sum(targetBranch, 1) + "..." + abox.getBranches().size() + "  from ABox.");
				}
				branches.subList( targetBranch, branches.size() ).clear();
				branchDeleted = true;


				// set the last clash before restore
				if (branch.getTryNext() < branch.getTryCount()) {
					branch.setLastClash(abox.getClash().getDepends());
				}

				// increment the counter
				branch.setTryNext(branch.getTryNext()+1);

				log.info( "JUMP: Branch " + targetBranch );
				if (targetBranch==117) {
					System.out.println("JUJU");
				}
				// no need to restore this branch if we exhausted possibilities
				if (branch.getTryNext() < branch.getTryCount()) {
					// undo the changes done after this branch
					restore(branch, abox.getClash().getDepends().time());
				}

			} else if (branchVar instanceof DisjunctionBranch) {
				DisjunctionBranch branch = (DisjunctionBranch) branchVar;

				Time intersection = Time.intersection(branch.getTryNextTime(), clashDS.time());

				if ( branch.getTryNext() < branch.getTryCount() ) {
					branch.setLastClash( abox.getClash().getDepends().partBy(intersection) );
				}

				branch.setTryNext(branch.getTryNext()+1);

				if (branch.currentlyUseless()) {
					if (!PelletOptions.SPECIAL_LOGS) {
						log.info("(SROIQ) soon will restore disj Branch(" +targetBranch+"). It is currently useless -> deleting later branches "+Integer.sum(targetBranch,1) + "..." + abox.getBranches().size() +"  from ABox.");
					} else {
						log.info("(SROIQ) soon will restore Branch(" + targetBranch + "). Deleting later branches " + Integer.sum(targetBranch, 1) + "..." + abox.getBranches().size() + "  from ABox.");
					}
					 abox.stats.backjumps += (branches.size() - targetBranch);
					branches.subList( targetBranch, branches.size() ).clear();
					branchDeleted = true;
				}


				log.info( "JUMP: Branch " + targetBranch );
				if (branch.getTryNext() < branch.getTryCount()) {
					restore(branch, intersection);
				}
			}

			// try the next possibility
			branchFound = branchVar.tryNext();

			if( !branchFound ) {
				log.info( "FAIL: Branch " + targetBranch );
//				if (branchVar instanceof DisjunctionBranch && ((DisjunctionBranch) branchVar).isUselessBranch()) {
//
//					branches.subList( targetBranch-1, branches.size() ).clear();
//				}
			}
		}

		return branchFound;
	}

	public void complete(Expressivity expr) {
		initialize( expr );

		while( !abox.isComplete() ) {
			while( abox.isChanged() && !abox.isClosed() ) {
				completionTimer.check();

				abox.setChanged( false );

				if( log.isLoggable( Level.INFO ) ) {
					log.info("------------------------------------------------------------");
					log.info( "Branch: " + abox.getBranch() + ", Depth: " + abox.stats.treeDepth
							+ ", Size: " + abox.getNodes().size());
					abox.validate();
//					printBlocked();
					abox.printTree();
				}

				IndividualIterator i = abox.getIndIterator();


				for( TableauRule tableauRule : tableauRules ) {
					tableauRule.apply( i );
					if( abox.isClosed() )
						break;
				}
			}


			if( abox.isClosed() ) {
				log.info( "Clash at Branch(" + abox.getBranch() + ") " + abox.getClash() +" (SROIQ)" );

				int currentBranch =  abox.getBranch();
				boolean backtrackSuccess = true;
				while (abox.getClash() != null && !abox.getClash().getDepends().isEmpty() && backtrackSuccess) {
					backtrackSuccess = backtrack();
				}

				if (backtrackSuccess) {
					abox.setClash( null );
					if (!branchDeleted) {
						log.info("Returned to Branch"+currentBranch);
						abox.setBranch(currentBranch);
					}
				} else {
					abox.setComplete(true);
				}

			} else {

				if( PelletOptions.SATURATE_TABLEAU ) {
					Branch unexploredBranch = null;
					for( int i = abox.getBranches().size() - 1; i >= 0; i-- ) {
						unexploredBranch = abox.getBranches().get( i );
//						ROBERT я изменил setTryNext в disj branch - учти тут
						unexploredBranch.setTryNext( unexploredBranch.getTryNext() + 1 );
						if( unexploredBranch.getTryNext() < unexploredBranch.getTryCount() ) {
							restore(unexploredBranch, abox.getClash().getDepends().time());
							System.out.println( "restoring branch " + unexploredBranch.getBranch()
									+ " tryNext = " + unexploredBranch.getTryNext()
									+ " tryCount = " + unexploredBranch.getTryCount() );
							unexploredBranch.tryNext();
							break;
						} else {
							System.out.println( "removing branch " + unexploredBranch.getBranch() );
							abox.getBranches().remove( i );
							unexploredBranch = null;
						}
					}
					if( unexploredBranch == null ) {
						abox.setComplete( true );
					}

				} else {

					abox.setComplete(true);
				}
			}
		}
		
	}

}
