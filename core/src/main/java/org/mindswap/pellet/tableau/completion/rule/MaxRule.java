// Copyright (c) 2006 - 2008, Clark & Parsia, LLC. <http://www.clarkparsia.com>
// This source code is available under the terms of the Affero General Public License v3.
//
// Please see LICENSE.txt for full license terms, including the availability of proprietary exceptions.
// Questions, comments, or requests for clarification: licensing@clarkparsia.com

package org.mindswap.pellet.tableau.completion.rule;

import java.util.AbstractMap;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.mindswap.pellet.Clash;
import org.mindswap.pellet.Edge;
import org.mindswap.pellet.EdgeList;
import org.mindswap.pellet.Individual;
import org.mindswap.pellet.Node;
import org.mindswap.pellet.NodeMerge;
import org.mindswap.pellet.PelletOptions;
import org.mindswap.pellet.Role;
import org.mindswap.pellet.Time;
import org.mindswap.pellet.TimeDS;
import org.mindswap.pellet.tableau.branch.MaxBranch;
import org.mindswap.pellet.tableau.completion.CompletionStrategy;
import org.mindswap.pellet.utils.SetUtils;

import aterm.ATermAppl;
import aterm.ATermInt;

import static org.mindswap.pellet.Time.getCardExceedEntry;

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
public class MaxRule extends AbstractTableauRule {
	public MaxRule(CompletionStrategy strategy) {
		super( strategy, BlockingType.INDIRECT );
	}

    /**
     * Apply max rule to the individual.
     */
    public void apply( Individual x ) {
        if( !x.canApply( Individual.MAX ) )
        	return;

        List<ATermAppl> maxCardinality = x.getTypes( Node.MAX );
        for (ATermAppl mc : maxCardinality) {

            applyMaxRule(x, mc);

            if (strategy.getABox().isClosed())
                return;

            if (x.isMerged())
                return;
        }
        x.applyNext[Individual.MAX] = maxCardinality.size();
    }
    
    protected void applyMaxRule( Individual x, ATermAppl mc ) {
 
        // max(r, n) is in normalized form not(min(p, n + 1))
        ATermAppl max = (ATermAppl) mc.getArgument( 0 );

        Role r = strategy.getABox().getRole( max.getArgument( 0 ) );
        int n = ((ATermInt) max.getArgument( 1 )).getInt() - 1;
        ATermAppl c = (ATermAppl) max.getArgument( 2 );

        TimeDS ds = x.getDepends( mc );

        if (ds.isEmpty()) {
            throw new RuntimeException("strange");
        }

        if (n==1) {
            applyFunctionalMaxRule(x, r, c, ds);
        } else {
            boolean hasMore = true;
            while (hasMore) {
                hasMore = applyMaxRule( x, r, c, n, ds );
                if (strategy.getABox().isClosed() || x.isMerged()) {
                    return;
                }
            }
        }

    }
    

    /**
     *
     * @return true if more merges are required for this maxCardinality
     */
    protected boolean applyMaxRule( Individual x, Role r, ATermAppl c, int k, TimeDS maxDS ) {
        EdgeList edges = x.getRNeighborEdges( r );
        Map<Node, TimeDS> neighbors = edges.getFilteredNeighborsAndTimeDS(x, c, maxDS.time());

        int n = neighbors.size();


        if( k == 0 && n > 0 ) {
            TimeDS clashTimeDS = TimeDS.empty();
            for (TimeDS timeDS : neighbors.values()) {
                clashTimeDS = clashTimeDS.union(TimeDS.intersection(timeDS, maxDS));
            }
            strategy.getABox().setClash(Clash.maxCardinality(x, clashTimeDS, r.getName(), 0));
            return false;
        }

        if( n <= k )
            return false;

        Map<Node, Time> neighborsTime = new HashMap<>();
        neighbors.forEach((node,d) -> neighborsTime.put(node, d.time()));

        Map.Entry<Time, Set<Node>> cardExceedEntry = getCardExceedEntry(neighborsTime, k);
        if (cardExceedEntry == null) {
            return false;
        }

        Time cardExceedTime = cardExceedEntry.getKey();
        Set<Node> nodes = cardExceedEntry.getValue();

        Time cardTime = nodes.stream().
                map(node -> neighbors.get(node).partBy(cardExceedTime).getFirstEntry().getKey()).
                reduce((a, b) -> Time.intersection(a, b)).orElse(null);

        n = nodes.size();
        if (!PelletOptions.SPECIAL_LOGS) {
            log.info("Neighbors: " + n + " maxCardinality: " + k);
            log.info("cardExceedEntry: " + cardExceedEntry + ", cardTime: " + cardTime);
        }

        if (cardTime == null) {
            throw new RuntimeException("MAX_RULE: STRNG BEHAVIOR IN CARDTIME...");
        }


        List<NodeMerge> mergePairs = new ArrayList<>();
        TimeDS differenceDS = findMergeNodes( nodes, x, mergePairs );
//        mergePairs.sort(Comparator.comparing((NodeMerge a) -> a.getSource().getName()).thenComparing(a -> a.getTarget().getName()));

        if( mergePairs.size() == 0 ) {
            TimeDS[] dependsArray = nodes.stream().map(neighbors::get).toArray(TimeDS[]::new);
            TimeDS clashDS = TimeDS.intersection(dependsArray);
            clashDS = TimeDS.intersection(clashDS, maxDS.partBy(cardTime));
            clashDS.unite(differenceDS.ds());

            log.info("Early clash detection for max rule worked " + x + " has more than "
                        + k + " " + r + " edges  ON  " + clashDS + "   "
                        + x.getRNeighborEdges(r).getNeighbors(x));

            if( strategy.getABox().doExplanation() )
                strategy.getABox().setClash( Clash.maxCardinality( x, clashDS, r.getName(), k ) );
            else
                strategy.getABox().setClash( Clash.maxCardinality( x, clashDS));

            return false;

        }


        // add the list of possible pairs to be merged in the branch list
        MaxBranch newBranch = new MaxBranch(strategy.getABox(), strategy, x, r, k, c, mergePairs, maxDS.partBy(cardTime));
        strategy.addBranch(newBranch);

        if (!newBranch.tryNext()) {
            return false;
        }

//        log.info("hasMore: " + "n="+n+" > k="+k+"+1");

        // if there were exactly k + 1 neighbors the previous step would
        // eliminate one node and only n neighbors would be left. This means
        // restriction is satisfied. If there were more than k + 1 neighbors
        // merging one pair would not be enough and more merges are required,
        // thus false is returned
        return n > k + 1;
    }


    TimeDS findMergeNodes( Set<Node> neighbors, Individual node, List<NodeMerge> pairs ) {
        TimeDS differenceDS = TimeDS.empty();

        List<Node> nodes = new ArrayList<Node>( neighbors );
        for( int i = 0; i < nodes.size(); i++ ) {
            Node y = nodes.get( i );
            for( int j = i + 1; j < nodes.size(); j++ ) {
                Node x = nodes.get( j );

                if( y.isDifferent( x ) ) {
                    differenceDS = differenceDS.union(y.getDifferenceDependency(x));
                    continue;
                }

                // 1. if x is a nominal node (of lower level), then Merge(y, x)
                if( x.getNominalLevel() < y.getNominalLevel() )
                    pairs.add( new NodeMerge( y, x ) );
                    // 2. if y is a nominal node or an ancestor of x, then Merge(x, y)
                else if( y.isNominal() )
                    pairs.add( new NodeMerge( x, y ) );
                    // 3. if y is an ancestor of x, then Merge(x, y)
                    // Note: y is an ancestor of x iff the max cardinality
                    // on node merges the "node"'s parent y with "node"'s
                    // child x
                else if( y.hasSuccessor( node ) )
                    pairs.add( new NodeMerge( x, y ) );
                    // 4. else Merge(y, x)
                else
                    pairs.add( new NodeMerge( y, x ) );
            }
        }

        return differenceDS;
    }


    public void applyFunctionalMaxRule(Individual x, Role s, ATermAppl c, TimeDS maxDS) {
        Set<Role> functionalSupers = s.getFunctionalSupers();
        if( functionalSupers.isEmpty() )
            functionalSupers = SetUtils.singleton( s );

        LOOP:
        for (Role r : functionalSupers) {

            if (PelletOptions.USE_TRACING) {
                maxDS.addExplain(s.getExplainSuper(r.getName()), strategy.getABox().doExplanation());
                maxDS.addExplain(r.getExplainFunctional(), strategy.getABox().doExplanation());
            }

            EdgeList edges = x.getRNeighborEdges( r );
            Map<Node, TimeDS> neighbors = edges.getFilteredNeighborsAndTimeDS(x, c, maxDS.time());

            neighbors.entrySet().removeIf(e -> e.getKey().isPruned());

            if (neighbors.size() <= 1)
                continue;


            Map<Node, Time> neighborsTime = new LinkedHashMap<>();
            neighbors.forEach((n, d) -> neighborsTime.put(n, d.time()));
            Map.Entry<Time, Set<Node>> cardExceedEntry = getCardExceedEntry(neighborsTime, 1);
            if (cardExceedEntry == null) {
                continue;
            }

            Time cardExceedTime = cardExceedEntry.getKey();
            Set<Node> nodes = cardExceedEntry.getValue();

            Time cardTime = nodes.stream().
                    map(node -> neighbors.get(node).partBy(cardExceedTime).getFirstEntry().getKey()).
                    reduce((a, b) -> Time.intersection(a, b)).orElse(null);

            if (!PelletOptions.SPECIAL_LOGS) {
                log.info("cardExceedEntry: " + cardExceedEntry + ", cardTime: " + cardTime);
            }

            if (cardTime == null) {
                throw new RuntimeException("MAX_RULE: STRNG BEHAVIOR IN CARDTIME...");
            }

            Iterator<Node> it = nodes.iterator();
            Node head = it.next();

            while (it.hasNext()) {
                Node next = it.next();
                if (head.isSame(next)) {
                    continue;
                }

                if (next.isDifferent(head)) {
                    TimeDS clashDS = TimeDS.intersection(maxDS.partBy(cardTime), neighbors.get(head), neighbors.get(next));
                    clashDS.unite(next.getDifferenceDependency(head).ds());

                    if (r.isFunctional())
                        strategy.getABox().setClash(Clash.functionalCardinality(x, clashDS, r.getName()));
                    else
                        strategy.getABox().setClash(Clash.maxCardinality(x, clashDS, r.getName(), 1));

                    break;
                }

                if (x.isNominal() && head.isBlockable() && next.isBlockable()
                        && head.hasSuccessor(x) && next.hasSuccessor(x)) {
                    Individual newNominal = strategy.createFreshIndividual( null, maxDS );

                    strategy.addEdge( x, r, newNominal, maxDS );

                    continue LOOP;
                }
                // always merge to a nominal (of lowest level) or an ancestor
                else if ((next.getNominalLevel() < head.getNominalLevel())
                        || (!head.isNominal() && next.hasSuccessor(x))) {
                    Node temp = head;
                    head = next;
                    next = temp;
                }

                TimeDS mergeDS = TimeDS.intersection(maxDS.partBy(cardTime), neighbors.get(head), neighbors.get(next));

                log.info("FUNC  " + x + " for prop " + r + " merge " + next + " -> " + head + "  ON  " + mergeDS);

                strategy.mergeTo(next, head, mergeDS);

                if (strategy.getABox().isClosed())
                    return;

                if (head.isPruned()) {
                    head = head.getSame();
                }
            }

        }
    }
}