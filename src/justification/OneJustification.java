package justification;

import formula.Formula;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.model.OWLOntology;

import org.semanticweb.owlapi.model.OWLAxiom;
import convertion.BackConverter;
import org.semanticweb.owlapi.reasoner.NodeSet;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import javafx.beans.property.ObjectProperty;
import org.apache.commons.lang3.builder.ToStringExclude;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.util.OWLEntityCollector;
import sun.reflect.generics.tree.ClassSignature;
import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.List;

public class OneJustification {
        public OneJustification(){

        }
        public List<Set<OWLAxiom>> computeOneJust(OWLOntology O, Set<OWLAxiom> S) throws Exception{

            List<Set<OWLAxiom>> ans = new ArrayList<>();
            for(OWLAxiom axiom : S){
               ans.add(computeOneJust(O,axiom));
            }
            return ans;
        }
        public  Set<OWLAxiom> computeOneJust(OWLOntology O, OWLAxiom axiom) throws Exception{
            expand ep = new expand();
            contract cr = new contract();

            Set<OWLAxiom> BigSets = ep.Expand(O,axiom);
            //Set<OWLAxiom> fin = cr.Contract(BigSets,axiom);
            return BigSets;


        }
        public  boolean entailed(OWLReasoner reasoner, OWLAxiom i){

            System.out.println(i);
            if (i instanceof OWLSubObjectPropertyOfAxiom){
                OWLSubObjectPropertyOfAxiom now = (OWLSubObjectPropertyOfAxiom) i;
                OWLObjectPropertyExpression sub = now.getSubProperty();
                OWLObjectPropertyExpression sup = now.getSuperProperty();
                NodeSet<OWLObjectPropertyExpression> superList = reasoner.getSuperObjectProperties(sub,false);
                //System.out.println(superList+" "+sup);
                return superList.containsEntity(sup);
            }
            else if( i instanceof  OWLClassAxiom)return reasoner.isEntailed(i);
            else{
                System.out.print("this is unknown type ");

            }
            return true;
        }
        OWLOntology computeModule(OWLOntology originalOnto,OWLAxiom eta) throws Exception{
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, originalOnto, ModuleType.STAR);
        Set<OWLAxiom> moduleAxioms = extractor.extract(eta.getSignature());
        return manager.createOntology(moduleAxioms);
        }
        public static  void main(String []args) throws  Exception{
            OneJustification JUST =  new OneJustification();
            OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
            String O2 = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/snomed_ct_intl_20170731.owl";
            String implicitWitness = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/witness_implicit.owl";
            String ui = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/ui.owl";
            OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));
            System.out.println(onto_2.getAxioms().size());
            OWLOntology onto_implicitWitness = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(implicitWitness));
            OWLOntology UI = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(ui));
            Set<OWLAxiom> axioms = onto_implicitWitness.getAxioms();
            for(OWLAxiom axiom : onto_implicitWitness.getAxioms()){
                System.out.println(axiom);
                if(axiom.toString().indexOf("96061006") != -1){
                    throw new Exception("FInd it!");
                }

                System.out.println("finished");

            }
            int num = 1;
            OWLReasoner reasoner= new Reasoner(new Configuration(),onto_2);

            //OWLReasoner reasoner = new ElkReasonerFactory().createReasoner(onto_2);
            for(OWLAxiom axiom : axioms){
                if(JUST.entailed(reasoner,axiom)){

                    System.out.println("yes1");
                }
                else{
                    System.out.println("no1");
                }
                System.out.println(num++);
                System.out.println("original :"+ axiom);
                OWLOntology module = JUST.computeModule(onto_2,axiom);
                Set<OWLAxiom> just = JUST.computeOneJust(module,axiom);
                System.out.println("just num:"+just.size());
                OWLOntology track = manager.createOntology(just);
                OWLReasoner reasoner2= new Reasoner(new Configuration(),track);

                //OWLReasoner reasoner2 = new ElkReasonerFactory().createReasoner(track);
                //OWLReasoner reasoner2 = new Reasoner.ReasonerFactory().createReasoner(track);
                if(JUST.entailed(reasoner2,axiom)){

                    System.out.println("yes2");
                }
                else{
                    System.out.println("no2");
                }
                reasoner2.dispose();

            }
            reasoner.dispose();
        }
}
