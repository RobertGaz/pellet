package org.mindswap.pellet.examples;

import aterm.ATermAppl;
import com.clarkparsia.pellet.owlapiv3.OWLAPILoader;
import com.clarkparsia.pellet.owlapiv3.PelletReasoner;
import com.clarkparsia.pellet.owlapiv3.PelletReasonerFactory;
import org.mindswap.pellet.ABox;
import org.mindswap.pellet.KBLoader;
import org.mindswap.pellet.KnowledgeBase;
import org.mindswap.pellet.RBox;
import org.mindswap.pellet.taxonomy.printer.ClassTreePrinter;
import org.mindswap.pellet.taxonomy.printer.TaxonomyPrinter;
import org.mindswap.pellet.tbox.TBox;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import java.io.File;
import java.util.Set;

public class Classes {
    private static final String fileName = "C:\\Users\\gaziz\\Desktop\\owl_samples\\liker.owl";

    public static void main(String[] args) throws Exception {

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology ontology = manager.loadOntologyFromOntologyDocument(new File(fileName));

        PelletReasoner reasoner = PelletReasonerFactory.getInstance().createReasoner(ontology);

        KnowledgeBase kb = reasoner.getKB();
        boolean con = kb.isConsistent();

        kb.classify();

        kb.realize();

        TaxonomyPrinter<ATermAppl> printer = new ClassTreePrinter();
        printer.print( kb.getTaxonomy() );

        System.out.println(con);

    }


}