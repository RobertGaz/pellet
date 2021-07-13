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

package org.mindswap.pellet;

import java.util.*;
import java.util.Map.Entry;

import java.util.logging.Level;
import java.util.logging.Logger;
import org.mindswap.pellet.exceptions.InternalReasonerException;
import org.mindswap.pellet.utils.ATermUtils;
import org.mindswap.pellet.utils.Bool;
import org.mindswap.pellet.utils.SetUtils;

import aterm.ATerm;
import aterm.ATermAppl;
import aterm.ATermList;

import com.clarkparsia.pellet.utils.CollectionUtils;

/**
 * @author Evren Sirin
 *
 */
public abstract class Node {
	public final static Logger log = Logger.getLogger( Node.class.getName() );
	
	public final static int BLOCKABLE = Integer.MAX_VALUE;
	public final static int NOMINAL   = 0;

	public final static int CHANGED   = 0x7F;
	public final static int UNCHANGED = 0x00;
	public final static int ATOM = 0;
	public final static int OR   = 1;
	public final static int SOME = 2;
	public final static int ALL  = 3;
	public final static int MIN  = 4;
	public final static int MAX  = 5;
	public final static int NOM  = 6;
	public final static int TYPES = 7;
	
	protected ABox abox;
	protected ATermAppl name;
	protected Map<ATermAppl, TimeDS> depends;
	private boolean isRoot;
	private boolean isConceptRoot;		
	
	/**
	 * If this node is merged to another one, points to that node otherwise
	 * points to itself. This is a linked list implementation of disjoint-union
	 * data structure.
	 */
	protected Node mergedTo = this;
    
    protected EdgeList inEdges;
	
	/**
	 * Dependency information about why merged happened (if at all)
	 */
	protected TimeDS mergeDepends = null;
	
	protected TimeDS pruned = null;
	
	/**
	 * Set of other nodes that have been merged to this node. Note that this 
	 * is only the set of nodes directly merged to this one. A recursive traversal
	 * is required to get all the merged nodes.
	 */
	protected Set<Node> merged;
	
	protected Map<Node, TimeDS> differents;
	
	protected Node(ATermAppl name, ABox abox) {
		this.name = name;
		this.abox = abox;		

		isRoot = !ATermUtils.isAnon( name );
		isConceptRoot = false;
		
		mergeDepends = TimeDS.INDEPENDENT();
		differents = CollectionUtils.makeMap();
		depends = CollectionUtils.makeMap();

        inEdges = new EdgeList();
	}

	protected Node(Node node, ABox abox) {
		this.name = node.getName();
		this.abox = abox;

		isRoot = node.isRoot;
		isConceptRoot = node.isConceptRoot;
		
		mergeDepends = node.mergeDepends;
		mergedTo = node.mergedTo;
		merged = node.merged;
		pruned = node.pruned;

		// do not copy differents right now because we need to
		// update node references later anyway
		differents = node.differents;
		depends = CollectionUtils.makeMap(node.depends);
		        
        inEdges = node.inEdges;
	}
	
	@Override
	public int hashCode() {
	    return name.hashCode();
	}
	
	@Override
	public boolean equals(Object obj) {
	    return (obj == this) || ((obj.getClass() == getClass()) && ((Node) obj).name.equals(name));
	}
	
	protected void updateNodeReferences() {
        mergedTo = abox.getNode( mergedTo.getName() );

        Map<Node, TimeDS> diffs = new HashMap<Node, TimeDS>( differents.size() );
        for(Map.Entry<Node, TimeDS> entry : differents.entrySet() ) {
            Node node = entry.getKey();

            diffs.put( abox.getNode( node.getName() ), entry.getValue() );
        }
        differents = diffs;

        if( merged != null ) {
            Set<Node> sames = new HashSet<Node>( merged.size() );
            for( Node node : merged ) {
                sames.add( abox.getNode( node.getName() ) );
            }
            merged = sames;
        }

		EdgeList oldEdges = inEdges;
		inEdges = new EdgeList(oldEdges.size());
		for(int i = 0; i < oldEdges.size(); i++) {
			Edge edge = oldEdges.edgeAt(i);

			Individual from = abox.getIndividual( edge.getFrom().getName() );
			Edge newEdge = new DefaultEdge( edge.getRole(), from, this, edge.getDepends() );

			inEdges.addEdge( newEdge );
			if( !isPruned() )
				from.getOutEdges().addEdge( newEdge );
		}
    }

	/**
	 * Indicates that node has been changed in a way that requires us to recheck
	 * the concepts of given type.
	 *  
	 * @param type type of concepts that need to be rechecked
	 */
	public void setChanged(int type) {
		// add node to effected list
		if( abox.getBranch() >= 0 && PelletOptions.TRACK_BRANCH_EFFECTS )
			abox.getBranchEffectTracker().add( abox.getBranch(), this.getName() );
	}	

	
	/**
	 * Returns true if this is the node created for the concept satisfiability check.
	 *  
	 * @return
	 */
	public boolean isConceptRoot() {
	    return isConceptRoot;
	}
	
	public void setConceptRoot( boolean isConceptRoot ) {
	    this.isConceptRoot = isConceptRoot;
	}
	
	public boolean isBnode() {
		return ATermUtils.isBnode( name );
	}

	public boolean isNamedIndividual() {
		return isRoot && !isConceptRoot && !isBnode();
	}
	
	public boolean isRoot() {
		return isRoot || isNominal();
	}	
	
	public abstract boolean isLeaf();
		
	public boolean isRootNominal() {
		return isRoot && isNominal();
	}
	
	public abstract Node copyTo(ABox abox);
	
	protected void addInEdge(Edge edge) {
        inEdges.addEdge( edge );
    }

    public EdgeList getInEdges() {
	    return inEdges;
    }	
    
    public boolean removeInEdge(Edge edge) {
        boolean removed = inEdges.removeEdge(edge);
        
        if( !removed ){
     		throw new InternalReasonerException("Trying to remove a non-existing edge " + edge);           
        }
        
        return true;
    }
    
    public void removeInEdges() {
        inEdges = new EdgeList();
    }

    public void reset(boolean onlyApplyTypes) {
    	assert onlyApplyTypes || isRootNominal() : "Only asserted individuals can be reset: " + this;

		if( onlyApplyTypes )
			return;
		
		if( isPruned() )
			unprune( DependencySet.NO_BRANCH );
		
    	mergedTo = this;
    	mergeDepends = TimeDS.INDEPENDENT();
    	merged = null;

    	//а  тут мы оставляем, ведь речь о differents
    	Iterator<TimeDS> i = differents.values().iterator();
    	while( i.hasNext()) {
			TimeDS d = i.next();
			if( d.getBranch() != DependencySet.NO_BRANCH ) {
				i.remove();
			}			    
		}
    	
    	resetTypes();
    	
    	inEdges.reset();
    }

    //РОБЕРТ
    protected void resetTypes() {
    	Iterator<TimeDS> i = depends.values().iterator();
    	while( i.hasNext()) {
    		TimeDS d = i.next();
//			if( d.getBranch() != DependencySet.NO_BRANCH ) {
//				i.remove();
//			}
		}
    }
    
	public Boolean restorePruned(int branch, Time time) {

		if( PelletOptions.TRACK_BRANCH_EFFECTS )
			abox.getBranchEffectTracker().add( abox.getBranch(), name );

		if( isPruned() ) {
			if (pruned.restoreByBranch(branch, time) && pruned.isEmpty()) {
				if (PelletOptions.RESTORE_LOGS)
					log.info("RESTORE: " + this + " merged node " + mergedTo + " " + mergeDepends);
//						(!PelletOptions.SPECIAL_LOGS ? " " + mergeDepends : ""));

				if (mergeDepends.restoreByBranch(branch, time) && mergeDepends.isEmpty()) {
					undoSetSame();
				}

				unprune(branch);

				return Boolean.TRUE;

			} else {
				if( log.isLoggable( Level.FINE ) )
					log.fine("DO NOT RESTORE: pruned node " + this + " = " + mergedTo + " " + mergeDepends);	

				return Boolean.FALSE;
			}
	    }
	    
	    return null;
	}
	
	
	public boolean restore(int branch, Time time) {
		if (this.toString().equals("Delicate")&&branch==117) {
			System.out.println("123");
		}
		if( PelletOptions.TRACK_BRANCH_EFFECTS )
			abox.getBranchEffectTracker().add( abox.getBranch(), name );

		boolean restored = false;
		
		List<ATermAppl> conjunctions = new ArrayList<>();

		for( Iterator<ATermAppl> i = getTypes().iterator(); i.hasNext(); ) {									
			ATermAppl c = i.next();	
			TimeDS timeDS = getDepends(c);

			boolean restoredTimeDS;
			if (PelletOptions.USE_SMART_RESTORE) {
				restoredTimeDS = timeDS.restoreByMax(branch, time);
			} else {
				restoredTimeDS = timeDS.restoreByBranch(branch, time);
			}

			if (restoredTimeDS) {
				restored = true;
				if (timeDS.isEmpty()) {
					if (PelletOptions.RESTORE_LOGS)
						log.info("RESTORE: " + this + " remove type " + ATermUtils.toString(c));
					i.remove();
					removeType(c);
				} else {
					if (PelletOptions.RESTORE_LOGS)
						log.info("RESTORE: " + this + " removed some time for type " + ATermUtils.toString(c));
				}
			} else if( PelletOptions.USE_SMART_RESTORE && ATermUtils.isAnd( c ) ) {
				conjunctions.add( c );
			}
		}

		
		// with smart restore there is a possibility that we remove a conjunct 
		// but not the conjunction. this is the case if conjunct was added before 
		// the conjunction but depended on an earlier branch. so we need to make
		// sure all conjunctions are actually applied
		if( PelletOptions.USE_SMART_RESTORE ) {
			for( Iterator<ATermAppl> i = conjunctions.iterator(); i.hasNext(); ) {
				ATermAppl c = i.next();
				TimeDS timeDS = getDepends(c);
				for(ATermList cs = (ATermList) c.getArgument(0); !cs.isEmpty(); cs = cs.getNext()) {
					ATermAppl conj = (ATermAppl) cs.getFirst();
					addType(conj, timeDS);
				}            
	        }
		}

		for( Iterator<Entry<Node,TimeDS>> i = differents.entrySet().iterator(); i.hasNext(); ) {
			Entry<Node,TimeDS> entry = i.next();
			Node node = entry.getKey();
			TimeDS timeDS = entry.getValue();

			if( timeDS.ds().getBranch() > branch ) {
				if (PelletOptions.RESTORE_LOGS)
					log.info("RESTORE: " + ATermUtils.toString(name) + " delete difference " + node);
				i.remove();
				restored = true;
			}

//			if (timeDS.restoreByBranch(branch, time)) {
//				restored = true;
//				if (timeDS.isEmpty()) {
//					log.info("RESTORE: " + ATermUtils.toString(name) + " delete difference " + node);
//					i.remove();
//				}
//			}

		}

		for( Iterator<Edge> i = inEdges.iterator(); i.hasNext(); ) {
			Edge e = i.next();
			TimeDS timeDS = e.getDepends();

			if (timeDS.restoreByBranch(branch, time)) {
				restored = true;
				if (timeDS.isEmpty()) {
					if (PelletOptions.RESTORE_LOGS)
						log.info("RESTORE: " + ATermUtils.toString(name) + " delete reverse edge " + (!PelletOptions.SPECIAL_LOGS ? e : ((DefaultEdge) e).printWithoutDS()));
					i.remove();
				} else {
					if (PelletOptions.RESTORE_LOGS)
						log.fine("RESTORE: " + ATermUtils.toString(name) + " removed some time of reverse edge");
				}
			}
		}

		return restored;
	}

	public TimeDS addType(ATermAppl c, TimeDS timeDS) {
		if (isPruned())
			throw new InternalReasonerException("Adding type to a pruned node " + this + " " + c);
		else if (isMerged())
			return null;
		if (timeDS.isEmpty()) {
			return null;
		}

	    // add to effected list
	    if( abox.getBranch() >= 0 && PelletOptions.TRACK_BRANCH_EFFECTS ) {
			abox.getBranchEffectTracker().add( abox.getBranch(), this.getName() );
		}
		
		int b = abox.getBranch();
		
		int max = timeDS.max();
		if(b == -1 && max != 0)
		    b = max + 1;

		timeDS = timeDS.copy( b );

		depends.putIfAbsent(c, TimeDS.empty());
		TimeDS added = depends.get(c).add(timeDS);

		if (!added.isEmpty()) {
			abox.setChanged(true);
			return added;
		}
		return null;
	}

	public boolean removeType(ATermAppl c) {
		return depends.remove(c) != null;
	}

	public boolean hasType(ATerm c) {
		return depends.containsKey(c);
	}
	
	public Bool hasObviousType(ATermAppl c) {
		TimeDS ds = getDepends( c );

		if( ds != null ) {
			if( ds.isIndependent() ) {
				return Bool.TRUE;
			}
		} else if( (ds = getDepends(ATermUtils.negate(c))) != null ) {
			if( ds.isIndependent() ) {
				return Bool.FALSE;
			}
		} else if( isIndividual() && ATermUtils.isNominal( c ) ) {
			// TODO probably redundant if : Bool.FALSE
			if( !c.getArgument( 0 ).equals( this.getName() ) ) {
				return Bool.FALSE;
			} else {
				return Bool.TRUE;
			}
		}

		if( isIndividual() ) {
			ATermAppl r = null;
			ATermAppl d = null;

			if( ATermUtils.isNot( c ) ) {
				final ATermAppl notC = (ATermAppl) c.getArgument( 0 );
				if( ATermUtils.isAllValues( notC ) ) {
					r = (ATermAppl) notC.getArgument( 0 );
					d = ATermUtils.negate( (ATermAppl) notC.getArgument( 1 ) );
				}
			}
			else if( ATermUtils.isSomeValues( c ) ) {
				r = (ATermAppl) c.getArgument( 0 );
				d = (ATermAppl) c.getArgument( 1 );
			}

			if( r != null ) {
				Individual ind = (Individual) this;

				Role role = abox.getRole( r );

				if( !role.isObjectRole() || !role.isSimple() ) {
					return Bool.UNKNOWN;
				}

				EdgeList edges = ind.getRNeighborEdges( role );

				Bool ot = Bool.FALSE;

				Time time = new Time();

				for( int e = 0; e < edges.size(); e++ ) {
					Edge edge = edges.edgeAt( e );

					if( !edge.getDepends().isIndependent() ) {
						ot = Bool.UNKNOWN;
						continue;
					}

					Individual y = (Individual) edge.getNeighbor( ind );

					// TODO all this stuff in one method - this is only for
					// handling AND
					// clauses - they are implemented in abox.isKnownType

					Bool condition = abox.isKnownType( y, d, SetUtils.<ATermAppl>emptySet());
					ot = ot.or(condition);// y.hasObviousType(d));

					if (condition.isTrue()) {
						time.unite(edge.getTime());
						if (time.isUniversal()) {
							break;
						}
					}
				}
				abox.setIsTypeTime(time);
				return ot;
			}
		}

		return Bool.UNKNOWN;
	}

	public boolean hasObviousType( Collection<ATermAppl> coll ) {
		for(Iterator<ATermAppl> i = coll.iterator(); i.hasNext();) {
            ATermAppl c = i.next();

			TimeDS ds = getDepends( c );
    		
    		if( ds != null && ds.isIndependent() )
    			return true;
        }
		
		return false;
	}			

	boolean hasPredecessor( Individual x ) {
		return x.hasSuccessor( this );
	}
	
	public abstract boolean hasSuccessor( Node x );
	
	public abstract TimeDS getNodeDepends();

	public abstract void setNodeDepends(TimeDS timeDS);

	public Map<ATermAppl, TimeDS> getDepends() {
		return depends;
	}

	public TimeDS getDepends(ATerm c) {
		TimeDS result = depends.get(c);
//		if (result != null && result.isEmpty()) {
//			throw new RuntimeException();
//		}
		if (result == null) {
			result = TimeDS.empty();
		}

		return result;

	}

	public TimeDS getDepends(ATerm c, Time time) {
		if (!depends.containsKey(c)) {
			return null;
		}
		return depends.get(c).partBy(time);
	}

	public Set<ATermAppl> getTypes() {
		return depends.keySet();
	}	

	public void removeTypes() {
		depends.clear();
	}

	public int prunedAt() {	    
		return pruned.getBranch();
	}
	
	public boolean isPruned() {
		return pruned != null && !pruned.isEmpty();
	}
	
	public TimeDS getPruned() {
		return pruned;
	}
		
	public abstract void prune(TimeDS ds);

	public void unprune( int branch ) {
        pruned = null;
        
        for(int i = 0; i < inEdges.size(); i++) {
            Edge edge = inEdges.edgeAt( i );

			TimeDS ds = edge.getDepends();
            if( ds.getBranch() <= branch ) {
                Individual pred = edge.getFrom();
                Role role = edge.getRole();

                // if both pred and *this* were merged to other nodes (in that order)
                // there is a chance we might duplicate the edge so first check for
                // the existence of the edge
                if( !pred.getOutEdges().hasExactEdge( pred, role, this ) ) {
                    pred.addOutEdge( edge );

                    // update affected
					if( PelletOptions.TRACK_BRANCH_EFFECTS ) {
						abox.getBranchEffectTracker().add( ds.getBranch(), pred.name );
						abox.getBranchEffectTracker().add( ds.getBranch(), name );
					}

					if (PelletOptions.RESTORE_LOGS)
						log.info( "RESTORE: " + ATermUtils.toString(name) + " add reverse edge " + (!PelletOptions.SPECIAL_LOGS ? edge : ((DefaultEdge) edge).printWithoutDS()));
                }
            }
        }
    }

	public abstract int getNominalLevel();
	
	public abstract boolean isNominal();
	
	public abstract boolean isBlockable();
	
	public abstract boolean isLiteral();
	
	public abstract boolean isIndividual();
	
	public int mergedAt() {	    
		return mergeDepends.getBranch();
	}
	
	public boolean isMerged() {
		return mergedTo != this;
	}

	public Node getMergedTo() {
		return mergedTo;
	}
	
//	public DependencySet getMergeDependency() {
//		return mergeDepends;
//	}
	
    /**
     * Get the dependency if this node is merged to another node. This
     * node may be merged to another node which is later merged to another 
     * node and so on. This function may return the dependency for the 
     * first step or the union of all steps.
     *
     */
    public TimeDS getMergeDependency( boolean all ) {
        if( !isMerged() || !all )
            return mergeDepends;

		TimeDS ds = mergeDepends;
        Node node = mergedTo;
        while( node.isMerged() ) {
            ds = TimeDS.union( ds, node.mergeDepends, abox.doExplanation() );
            node = node.mergedTo;            
        }
        
        return ds;
    }
    
	public Node getSame() {
		if(mergedTo == this)
			return this;
		
		return mergedTo.getSame();
	}
	
	public void undoSetSame() {
		mergedTo.removeMerged( this );
		mergeDepends = TimeDS.INDEPENDENT();
		mergedTo = this;	    
	}
	
	private void addMerged( Node node ) {
	    if( merged == null )
	        merged = new HashSet<Node>( 3 );
	    merged.add( node );
	}
		
	public Set<Node> getMerged() {
		if ( merged == null )
			return SetUtils.emptySet();
	    return merged;
	}
	
	public Map<Node,TimeDS> getAllMerged() {
		Map<Node,TimeDS> result = new HashMap<Node,TimeDS>();
		getAllMerged( TimeDS.INDEPENDENT(), result );
		return result;
	}
	
	private void getAllMerged(TimeDS ds, Map<Node,TimeDS> result) {
		if ( merged == null )
			return;
		
		for( Node mergedNode : merged ) {
			TimeDS mergeDS = TimeDS.union(ds, mergedNode.getMergeDependency( false ), false );
			result.put( mergedNode, mergeDS );
			mergedNode.getAllMerged( mergeDS, result );
		}		
	}
	
	private void removeMerged( Node node ) {
	    merged.remove( node );
	    if( merged.isEmpty() )
	        merged = null; // free space
	}
	
	public boolean setSame(Node node, TimeDS mergeDS) {
		if( isSame( node ) ) 
		    return false;
        if( isDifferent( node ) ) {
        	abox.setClash( Clash.nominal( this, mergeDS, node.getName() ) );
		    return false;
		}
		
		mergedTo = node;
		mergeDepends = mergeDS.copy( abox.getBranch() );
		node.addMerged( this );
		return true;
	}
	
	public boolean isSame(Node node) {
		return getSame().equals( node.getSame() );
	}
		
	public boolean isDifferent( Node node ) {
		return differents.containsKey(node);
	}
		
	public Set<Node> getDifferents() {
		return differents.keySet();
	}

	public TimeDS getDifferenceDependency(Node node) {
		return differents.get(node);
	}	

	public boolean setDifferent(Node node, TimeDS ds) {

		// add to effected list
		if( abox.getBranch() >= 0 && PelletOptions.TRACK_BRANCH_EFFECTS )
			abox.getBranchEffectTracker().add( abox.getBranch(), node.getName() );

		if( isDifferent( node ) )
			return false;
		if( isSame( node ) ) {
			ds = TimeDS.union( ds, this.getMergeDependency( true ), abox.doExplanation() );
			ds = TimeDS.union( ds, node.getMergeDependency( true ), abox.doExplanation() );
			abox.setClash( Clash.nominal( this, ds, node.getName() ));

			if (!ds.isIndependent()) {
				return false;
			}
		}
		
		ds = ds.copy( abox.getBranch() );
		differents.put(node, ds);
		node.setDifferent(this, ds);
		abox.setChanged( true );
		return true;
	}
	
	public void inheritDifferents( Node y, TimeDS mergeDS ) {
    	assert mergeDS.size() == 1;
		for( Map.Entry<Node,TimeDS> entry : y.differents.entrySet() ) {
			Node yDiff = entry.getKey();
			TimeDS finalDS = entry.getValue().union(mergeDS.ds(), abox.doExplanation());
			
			setDifferent( yDiff, finalDS );
		}
	}

	public ATermAppl getName() {
		return name;
	}
	
	public abstract ATermAppl getTerm();
	
	public String getNameStr() {
		return name.getName();
	}
	
	public String toString() {
		return ATermUtils.toString( name );
	}
	
	/**
	 * A string that identifies this node either using its name or the path
	 * of individuals that comes to this node. For example, a node that has
	 * been generated by the completion rules needs to be identified with
	 * respect to a named individual. Ultimately, we need the shortest path
	 * or something like that but right now we just use the first inEdge 
	 * 
	 * @return
	 */
	public List<ATermAppl> getPath() {	
	    LinkedList<ATermAppl> path = new LinkedList<ATermAppl>();

        if(isNamedIndividual()) 
            path.add(name);
	    else {
            Set<Node> cycle = new HashSet<Node>();
		    Node node = this;
		    while(!node.getInEdges().isEmpty()) {
		        Edge inEdge = node.getInEdges().edgeAt(0);
		        node = inEdge.getFrom();
                if( cycle.contains( node ) )
                    break;
                else
                    cycle.add( node );
	            path.addFirst( inEdge.getRole().getName() );
                if( node.isNamedIndividual() ) {
                    path.addFirst( node.getName() );
                    break;
                }
		    }
	    }
	    
		
		return path;
	}
	

	/**
	 * getABox
	 * 
	 * @return
	 */
	public ABox getABox() {
		return abox;
	}
}

