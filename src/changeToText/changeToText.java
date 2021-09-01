package changeToText;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;

import java.io.File;
import java.util.Set;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.*;

public class changeToText {
    public static void main(String[] args) throws Exception{
        String O2 = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/snomed_ct_intl_20170731.owl";
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));
        Set<OWLAxiom> axioms = onto_2.getAxioms();
        System.out.println(1);
        FileOutputStream fos = new FileOutputStream("/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/0731_3.txt",true);

        for(OWLAxiom axiom : axioms){
            String now = axiom.toString();
         if(now.contains("id/96061006")){
                System.out.println(now);
                fos.write(axiom.toString().getBytes());
                fos.write('\n');
         }
         if(now.contains("377419009")){
                System.out.println(now);
                fos.write(axiom.toString().getBytes());
                fos.write('\n');
         }
            //fos.write(axiom.toString().getBytes());
           // fos.write('\t');
        }
       fos.close();


    }
}
