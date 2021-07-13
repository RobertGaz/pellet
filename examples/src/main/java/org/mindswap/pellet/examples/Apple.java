package org.mindswap.pellet.examples;

import com.clarkparsia.pellet.owlapiv3.OWLAPILoader;
import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import org.mindswap.pellet.ABox;
import org.mindswap.pellet.KBLoader;
import org.mindswap.pellet.KnowledgeBase;
import org.mindswap.pellet.RBox;
import org.mindswap.pellet.tbox.TBox;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.io.File;
import java.util.Set;

public class Apple {
    private static final String fileName = "C:\\Users\\gaziz\\Desktop\\owl_samples\\func.owl";

    public static void main(String[] args) throws Exception {

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(fileName));

        PelletReasoner reasoner = PelletReasonerFactory.getInstance().createReasoner(ontology);

        KnowledgeBase kb = reasoner.getKB();
        boolean con = kb.isConsistent();

        System.out.println(con);
    }


}