package org.mindswap.pellet.examples;

import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import org.mindswap.pellet.*;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.formats.RDFXMLDocumentFormat;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import java.io.File;
import java.io.FileOutputStream;

public class Okay {
//    private static final String fileName = "C:\\Users\\gaziz\\Desktop\\bundle2\\simple-galen.owl";
//    private static final String fileName = "C:\\Users\\gaziz\\Desktop\\pikaperProps.owl";
//    private static final String fileName = "C:\\Users\\gaziz\\Desktop\\func.owl";
//        private static final String fileName = "C:\\Users\\gaziz\\Desktop\\pikap3.owl";
//private static final String fileName = "C:\\Users\\gaziz\\Desktop\\bundle2\\wine.owl";
private static final String fileName = "C:\\Users\\gaziz\\Desktop\\pikapProp.owl";
//private static final String fileName = "C:\\Users\\gaziz\\Desktop\\bundle2\\people_pets.owl";
    public static void main(String[] args) throws Exception {

        PelletOptions.SPECIAL_LOGS = true;

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(fileName));

        PelletReasoner reasoner = PelletReasonerFactory.getInstance().createReasoner(ontology);
        KnowledgeBase kb = reasoner.getKB();
        boolean con = kb.isConsistent();

        System.out.println(con);

    }


}