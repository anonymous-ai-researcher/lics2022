package Test;

import com.google.common.collect.Sets;
import convertion.Converter;
import elk.elkEntailment;
import forgetting.Forgetter;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.EntailmentChecker;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;
import javafx.util.*;
import java.io.File;
import java.util.*;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.TopConcept;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;
import connectives.And;
import connectives.Or;

import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import formula.Formula;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

public class statistical {
    public static  void entail()throws Exception{
        OWLOntology ui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/017010180.owl"));
        System.out.println("loaded");
        OWLOntology onto1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201601.owl"));
        //OWLReasoner 	reasoner = new ElkReasonerFactory().createReasoner(onto1);
        OWLReasoner reasoner= new Reasoner(new Configuration(),onto1);

        System.out.println("loaded3");

        int step = 1;
        int witness = 0;
        for(OWLAxiom axiom : ui.getLogicalAxioms()){
            System.out.println(step+" "+ui.getLogicalAxioms().size());
            step++;
            if(elkEntailment.entailed(reasoner,axiom)){

            }
            else{
                witness++;
                System.out.println("witness "+witness);
            }
        }

    }
    public static void beforeafter() throws   Exception{
        OWLOntology ui = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/0160101701.owl"));
        System.out.println("loaded");
        OWLOntology onto_1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201601.owl"));
        System.out.println("loaded");
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_201701.owl"));
        System.out.println("loaded");
        Converter ct = new Converter();
        BackConverter bc = new BackConverter();


        Set<OWLClass> c_sig_1 = onto_1.getClassesInSignature();
        Set<OWLClass> c_sig_2 = onto_2.getClassesInSignature();
        System.out.println(onto_1.getLogicalAxioms().size()+" "+onto_2.getLogicalAxioms().size());
        Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(c_sig_2, c_sig_1));
        Set<OWLObjectProperty> r_sig_1 = onto_1.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig_2 = onto_2.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(r_sig_2, r_sig_1));

        Set<OWLEntity> forgettingSignatures = new HashSet<>();
        forgettingSignatures.addAll(r_sig);
        forgettingSignatures.addAll(c_sig);
        // Extract module to speed our tool on common signature.
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(OWLManager.createOWLOntologyManager(), onto_2, ModuleType.BOT);
        Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto_2.getSignature(),forgettingSignatures));
        Set<OWLLogicalAxiom>moduleOnto_2_OnCommonSig_logical = new HashSet<>();

        for(OWLAxiom axiom : moduleOnto_2OnForgettingSig){
            if(axiom instanceof OWLLogicalAxiom){
                moduleOnto_2_OnCommonSig_logical.add((OWLLogicalAxiom)axiom);
            }
        }
        System.out.println("module size "+moduleOnto_2_OnCommonSig_logical.size()+"  o2 size "+ onto_2.getLogicalAxioms().size());



        Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
        Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);

        //List<Formula> formula_list = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical_temp);
        List<Formula> formula_list = ct.AxiomsConverter(moduleOnto_2_OnCommonSig_logical);

        System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                + role_set.size() + "] role names from [" + formula_list.size() + "] normalized axioms");

        OWLOntology onto_22 = bc.toOWLOntology(formula_list);
        System.out.println("before "+ Sets.difference(onto_22.getLogicalAxioms(),ui.getLogicalAxioms()).size());
        System.out.println("after "+ Sets.difference(ui.getLogicalAxioms(),onto_22.getLogicalAxioms()).size());

        /*
        int before = 0,after = 0,step = 0;
        for(Formula formula: formula_list){
            OWLAxiom a = bc.toOWLAxiom(formula);
            if(Sets.intersection(a.getSignature(),forgettingSignatures).size()!=0) before++;
            System.out.println(step+" "+formula_list.size());
            step++;
        }
        for(Formula formula: uilist){
            OWLAxiom a = bc.toOWLAxiom(formula);
            if(Sets.intersection(a.getSignature(),forgettingSignatures).size()!=0) after++;
            System.out.println(step+" "+formula_list.size());
            step++;
        }
        System.out.println("before1 "+before+" after1 "+ after);

         */
        List<Formula> uilist = ct.OntologyConverter(ui);

        System.out.println("before "+ Sets.difference(new HashSet<>(formula_list),new HashSet<>(uilist)).size());
        System.out.println("after "+ Sets.difference(new HashSet<>(uilist),new HashSet<>(formula_list)).size());
        System.out.println(formula_list.size()+" "+uilist.size());
    }
    public static void metricSNOMED()throws  Exception{
        OWLOntology onto_1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_202007.owl"));
        System.out.println("load1");
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/ontology_202003.owl"));
        System.out.println("load1");
        Set<OWLClass> c_sig_1 = onto_1.getClassesInSignature();
        Set<OWLClass> c_sig_2 = onto_2.getClassesInSignature();
        System.out.println(onto_1.getLogicalAxioms().size()+" "+onto_2.getLogicalAxioms().size());
        Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(c_sig_2, c_sig_1));
        Set<OWLObjectProperty> r_sig_1 = onto_1.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig_2 = onto_2.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(r_sig_2, r_sig_1));

        Set<OWLEntity> forgettingSignatures = new HashSet<>();
        forgettingSignatures.addAll(r_sig);
        forgettingSignatures.addAll(c_sig);
        // Extract module to speed our tool on common signature.
        SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(OWLManager.createOWLOntologyManager(), onto_2, ModuleType.STAR);
        Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(Sets.difference(onto_2.getSignature(),forgettingSignatures));
        Set<OWLLogicalAxiom>moduleOnto_2_OnCommonSig_logical = new HashSet<>();

        for(OWLAxiom axiom : moduleOnto_2OnForgettingSig){
            if(axiom instanceof OWLLogicalAxiom){
                moduleOnto_2_OnCommonSig_logical.add((OWLLogicalAxiom)axiom);
            }
        }
        System.out.println("module size "+moduleOnto_2_OnCommonSig_logical.size()+"  o2 size "+ onto_2.getLogicalAxioms().size());


        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        Forgetter forgetter = new Forgetter();

        Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
        Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);

        //List<Formula> formula_list = ct.AxiomsConverter(moduleOnto_2OnCommonSig_logical_temp);
        List<Formula> formula_list = ct.AxiomsConverter(moduleOnto_2_OnCommonSig_logical);

        System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                + role_set.size() + "] role names from [" + formula_list.size() + "] normalized axioms");
    }
    public static void merge()throws Exception{
        OWLOntology implicitwitness = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/19011801_witness_implicit.owl"));
        OWLOntology explicitwitness = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_logical_difference/Test_Data/all/19011801_witness_explicit.owl"));
        Converter ct = new Converter();
        List<Formula> formulas1 = ct.OntologyConverter(implicitwitness);
        List<Formula>formulas2 = ct.OntologyConverter(explicitwitness);
        int t = Sets.difference(new HashSet<>(formulas1),new HashSet<>(formulas2)).size();
        System.out.println(t);
        System.out.println(formulas1.size());
        System.out.println(explicitwitness.getLogicalAxioms().size());
        System.out.println(t+explicitwitness.getLogicalAxioms().size());
    }

    public static  void main(String [] args) throws Exception{
        beforeafter();
        /*
        HashMap<OWLAxiom,Integer> now = new HashMap<>();
        BackConverter bc = new BackConverter();

        OWLOntology onto =  OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(
                "/Users/liuzhao/Desktop/experiments/Test_data_for_forgetting/TestData/Corpus_3/00117.owl"));

        Set<OWLClass> concepts = onto.getClassesInSignature();
        HashMap<OWLClass,HashSet<OWLClass>> map = new HashMap<>();
        Set<OWLAxiom> newAxioms = new HashSet<>();
        for(OWLAxiom axiom : onto.getLogicalAxioms()){
            if(axiom instanceof OWLEquivalentClassesAxiom){
              //  newAxioms.addAll(((OWLEquivalentClassesAxiom) axiom).asOWLSubClassOfAxioms());
            }
            else{
                newAxioms.add(axiom);
            }
        }
        for(OWLAxiom axiom : newAxioms){
            if(axiom instanceof OWLSubClassOfAxiom){
                OWLSubClassOfAxiom axiom1 = (OWLSubClassOfAxiom) axiom;
                Set<OWLClass> templ = axiom1.getSubClass().getClassesInSignature();
                Set<OWLClass> tempr = axiom1.getSuperClass().getClassesInSignature();
                for(OWLClass c : templ){
                    if(map.containsKey(c)){
                        HashSet<OWLClass> te = map.get(c);
                        te.addAll(tempr);
                        map.put(c,te);
                    }
                    else{
                        HashSet<OWLClass> te = new HashSet<>();
                        te.addAll(tempr);
                        map.put(c,te);
                    }
                }

            }

        }
        for(OWLClass c1 : concepts){
            for(OWLClass c2: concepts){
                if(map.containsKey(c1) && map.get(c1).contains(c2) && map.containsKey(c2) && map.get(c2).contains(c1)){
                    System.out.println(c1+" "+c2);
                }
            }
        }
        System.out.println("-------------");
        for(OWLClass c1 : concepts){
            for(OWLClass c2: concepts) {
                for (OWLClass c3 : concepts) {

                    if (map.containsKey(c1) && map.get(c1).contains(c2) && map.containsKey(c2) && map.get(c2).contains(c3) &&map.containsKey(c3) && map.get(c3).contains(c1)) {
                        System.out.println(c1 + " " + c2+" "+c3);
                    }
                }
            }
        }
        System.out.println("-------------");

        Set<OWLObjectProperty> roles = onto.getObjectPropertiesInSignature();
        map = new HashMap<>();
        Set<OWLAxiom> newAxioms2 = new HashSet<>();
        for(OWLAxiom axiom : onto.getLogicalAxioms()){
            if(axiom instanceof OWLEquivalentClassesAxiom){
                //newAxioms.addAll(((OWLEquivalentClassesAxiom) axiom).asOWLSubClassOfAxioms());
            }
            else{
                newAxioms2.add(axiom);
            }
        }
        for(OWLAxiom axiom : newAxioms2){
            if(axiom instanceof OWLSubClassOfAxiom){
                OWLSubClassOfAxiom axiom1 = (OWLSubClassOfAxiom) axiom;
                Set<OWLClass> templ = axiom1.getSubClass().getClassesInSignature();
                Set<OWLClass> tempr = axiom1.getSuperClass().getClassesInSignature();
                for(OWLClass c : templ){
                    if(map.containsKey(c)){
                        HashSet<OWLClass> te = map.get(c);
                        te.addAll(tempr);
                        map.put(c,te);
                    }
                    else{
                        HashSet<OWLClass> te = new HashSet<>();
                        te.addAll(tempr);
                        map.put(c,te);
                    }
                }

            }

        }
        System.out.println("-------------");

        for(OWLObjectProperty r1 : roles){
            for(OWLObjectProperty r2: roles){
                if(map.containsKey(r1) && map.get(r1).contains(r2) && map.containsKey(r2) && map.get(r2).contains(r1)){
                    System.out.println(r1+" "+r2);
                }
            }
        }
        for(OWLObjectProperty r1 : roles){
            for(OWLObjectProperty r2: roles) {
                for (OWLObjectProperty r3 : roles) {

                    if (map.containsKey(r1) && map.get(r1).contains(r2) && map.containsKey(r2) && map.get(r2).contains(r3) &&map.containsKey(r3) && map.get(r3).contains(r1)) {
                        System.out.println(r1 + " " + r2+" "+r3);
                    }
                }
            }
        }
        System.out.println("-------------");
*/
    }
}
