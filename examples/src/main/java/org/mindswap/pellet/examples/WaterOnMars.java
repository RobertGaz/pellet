package org.mindswap.pellet.examples;

import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import org.mindswap.pellet.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.io.File;
import java.util.logging.Logger;

public class WaterOnMars {
    public final static Logger log = Logger.getLogger( WaterOnMars.class.getName() );

    private static final File inputDir = new File("C:\\Users\\gaziz\\Desktop\\bundle1\\");

    public static void main(String[] args) throws Exception {
        File[] inputFiles = inputDir.listFiles();
        int cnt = 1;
        for (File file : inputFiles) {
            log.info("*******************************************************************************************************************************");
            log.info("\n\n\n\n");
            log.info("OWL ONTOLOGY  #"+cnt + " / " + inputFiles.length + ".      "+file.getName()+"\n");
            checkConsistency(file);
            cnt++;
        }
    }

    private static void checkConsistency(File file) throws Exception {
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(file);
        PelletReasoner reasoner = PelletReasonerFactory.getInstance().createReasoner(ontology);
        KnowledgeBase kb = reasoner.getKB();
        kb.isConsistent();
    }



}