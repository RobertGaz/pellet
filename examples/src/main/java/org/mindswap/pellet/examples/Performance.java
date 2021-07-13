package org.mindswap.pellet.examples;

import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import org.mindswap.pellet.KnowledgeBase;
import org.mindswap.pellet.utils.Stat;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

public class Performance {
    private static final String ontologiesDirectory = "C:\\Users\\gaziz\\Desktop\\bundle\\timeDS\\";

    private static int CALL_COUNT = 100;

    public static void main(String[] args) throws Exception {
        File dir = new File(ontologiesDirectory);
        for (File file : dir.listFiles()) {
            processOntology(file);
        }
    }

    private static void processOntology(File file) throws Exception {
        OWLOntologyManager ontologyManager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = ontologyManager.loadOntologyFromOntologyDocument(file);

        List<Stat> stats = new ArrayList<>();
        for (int i = 0; i < CALL_COUNT; i++) {
            PelletReasoner reasoner = PelletReasonerFactory.getInstance().createReasoner(ontology);
            KnowledgeBase kb = reasoner.getKB();
            kb.isConsistent();
            Stat stat = kb.getStat();
            stats.add(stat);
//            System.out.println(stat);
        }


        String s = file.getName() +
                " Result: " + (stats.get(0).error ? "ERROR" : stats.get(0).result) +
                ". Time: " + (int) stats.stream().mapToLong(stat -> stat.time).filter(val -> val>0).average().orElse(-1) +
                ". Memory: " + (int) stats.stream().mapToLong(stat -> stat.memory/1000).filter(val -> val>0).average().orElse(-1) +
                "kb. Nodes before: " + stats.get(0).treeSize_1 +
                ", after: " + stats.get(0).treeSize_2 +
                ". Branches: " + stats.get(0).branches +
                ", backtracks: " + stats.get(0).backtracks +
                ", backjumps: " + stats.get(0).backjumps;

        System.out.println(s);
    }
}
