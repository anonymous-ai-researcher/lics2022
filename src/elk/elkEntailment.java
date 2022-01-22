package elk;

import BackTrack.BackTrack;
import Test.TestForgetting;
import com.google.common.collect.Sets;
import concepts.AtomicConcept;
import convertion.BackConverter;
import formula.*;
import forgetting.LDiff;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;

import java.io.File;
import java.util.*;
public class elkEntailment {
    public static HashMap<OWLAxiom,Boolean>hasChecked_OnO2 = new HashMap<>();
    public static void check(OWLOntology onto,OWLOntology result,Set<OWLEntity> signature)throws Exception{
        if(Sets.intersection(result.getSignature(),signature).size() != 0){
            throw new Exception();
        }
        Reasoner reasoner = new Reasoner(new Configuration(),onto);
        for(OWLAxiom axiom : result.getLogicalAxioms()){
            if(!reasoner.isEntailed(axiom)){
                throw new Exception();
            }
        }
    }
    public static void check(OWLOntology onto, List<Formula> ui, Set<AtomicRole> roleSet, Set<AtomicConcept> conceptSet)throws Exception{

        OWLReasoner reasoner = new Reasoner(new Configuration(),onto);
        System.out.println("-------");
        BackConverter ct = new BackConverter();
        int all = ui.size();
        int i = 0 ;
        for(Formula formula : ui){
            /*
            if(Sets.intersection(formula.get_c_sig(),conceptSet).size() != 0 || Sets.intersection(formula.get_r_sig(),roleSet).size() != 0){
                System.out.println(formula);
                throw new Exception("there exits new symbols!");

            }

             */
            OWLAxiom axiom = ct.toOWLAxiom(formula);
            if(!reasoner.isEntailed(axiom)){
                System.out.println(formula);
                System.out.println(axiom);
                throw new Exception("there is an axiom not entailed by initial onto!");
            }
            System.out.println("yes "+ i++ +" " + all);

        }
    }
    public  static boolean  entailed(OWLReasoner reasoner, OWLAxiom i  ){
        //return reasoner.isEntailed(i);
        if(i.toString().contains("Definer")) return false;

        boolean isentailed = false;
        if (i instanceof OWLSubObjectPropertyOfAxiom){
            OWLSubObjectPropertyOfAxiom now = (OWLSubObjectPropertyOfAxiom) i;
            OWLObjectPropertyExpression sub = now.getSubProperty();
            OWLObjectPropertyExpression sup = now.getSuperProperty();
            if(sub.equals(sup)) isentailed = true;
            else {
                NodeSet<OWLObjectPropertyExpression> superList = reasoner.getSuperObjectProperties(sub, false);

                isentailed = superList.containsEntity(sup);
            }
        }
        else if( i instanceof OWLClassAxiom)  isentailed =  reasoner.isEntailed(i);
        else{
            System.out.print("this is unknown type ");

        }

        return isentailed;


    }
    //this function uses a cache to avoid checking the axioms which had been checked before. This function only been used while forgetting.
    public  static boolean  entailed(OWLReasoner reasoner, OWLAxiom i ,Integer tag ){
        if(i.toString().contains("Definer")) return false;
        if(tag == 2 && hasChecked_OnO2.containsKey(i)){

            return hasChecked_OnO2.get(i);
        }

        boolean isentailed = false;
        isentailed = reasoner. isEntailed(i);
        /*
        if (i instanceof OWLSubObjectPropertyOfAxiom){
            OWLSubObjectPropertyOfAxiom now = (OWLSubObjectPropertyOfAxiom) i;
            OWLObjectPropertyExpression sub = now.getSubProperty();
            OWLObjectPropertyExpression sup = now.getSuperProperty();
            if(sub.equals(sup)) isentailed = true;
            else {
                NodeSet<OWLObjectPropertyExpression> superList = reasoner.getSuperObjectProperties(sub, false);

                isentailed = superList.containsEntity(sup);
            }
        }
        else if( i instanceof OWLClassAxiom)  isentailed =  reasoner.isEntailed(i);
        else{
            System.out.print("this is unknown type ");

        }

         */


        //boolean isentailed = reasoner.isEntailed(i);
        if(tag == 2){
            hasChecked_OnO2.put(i,isentailed);
        }
        return isentailed;
    }




    public static void main(String [] args) throws Exception{

        OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();
        System.out.println("Onto_2 Path: ");
        String filePath2 = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/snomed_ct_intl_20170731.owl";
        OWLOntology onto_2 = manager2.loadOntologyFromOntologyDocument(new File(filePath2));

        OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();
        System.out.println("ui Path: ");
        String filePath1 = "/Users/liuzhao/nju/NCBO/data/snomedcttest/snomed_ct_intl_20170731.owl/ui.owl";
        OWLOntology ui = manager1.loadOntologyFromOntologyDocument(new File(filePath1));

        System.out.println(onto_2.getLogicalAxioms().size()+" "+ui.getLogicalAxioms().size());
    }
}
