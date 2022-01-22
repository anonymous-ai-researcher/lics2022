
package apiForPy;
import com.google.common.collect.Sets;
import connectives.Inclusion;
import forgetting.Fame;
import forgetting.Forgetter;
import forgetting.LDiff;
import forgetting.saveMetrics;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import org.omg.Messaging.SYNC_WITH_TRANSPORT;
//import org.semanticweb.HermiT.Reasoner;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.OWLOntologyDocumentSource;
import org.semanticweb.owlapi.io.OWLOntologyDocumentTarget;
//import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.*;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import simplification.*;
import roles.AtomicRole;
import concepts.AtomicConcept;
import convertion.*;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

import java.io.*;
import java.text.Normalizer;
import java.util.*;

public class showData {
    static{
        System.out.println("api  for py");
    }
    public void INIT(){
        //DefinerIntroducer.owldefiner_set = new LinkedHashSet<>();;
        //DefinerIntroducer.definer_set = new HashSet<>();
    }
    public List<List> computingLDiff(String O2,String O1)throws Exception{
        OWLOntology onto_1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O1));
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));
        LDiff ld = new LDiff();
        List<OWLOntology> ans = ld.LDiff(onto_1,onto_2);
        Converter bc = new Converter();
        List<List> re = new ArrayList<>();
        re.add(bc.OntologyConverter(ans.get(1)));
        re.add(bc.OntologyConverter(ans.get(2)));
        re.add(bc.OntologyConverter(ans.get(3)));
        re.add(Collections.singletonList(1-Forgetter.isExtra));
        return re;
    }
    /*
    public List<List> computingLDiff(String O2,String O1)
            throws Exception {
        INIT();
        OWLOntology onto_1 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O1));
        OWLOntology onto_2 = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(O2));

        Set<OWLClass> c_sig_1 = onto_1.getClassesInSignature();
        Set<OWLClass> c_sig_2 = onto_2.getClassesInSignature();
        Set<OWLClass> c_sig = new LinkedHashSet<>(Sets.difference(c_sig_2, c_sig_1));
        Set<OWLObjectProperty> r_sig_1 = onto_1.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig_2 = onto_2.getObjectPropertiesInSignature();
        Set<OWLObjectProperty> r_sig = new LinkedHashSet<>(Sets.difference(r_sig_2, r_sig_1));

        Converter ct = new Converter();
        BackConverter bc = new BackConverter();
        //Simplifier pp = new Simplifier();
        Forgetter forgetter = new Forgetter();

        Set<AtomicRole> role_set = ct.getRolesfromObjectProperties(r_sig);
        Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);

        Set<OWLLogicalAxiom> owlAxiom_set = Sets.difference(onto_2.getLogicalAxioms(), onto_1.getLogicalAxioms());

        List<Formula> formula_list = ct.AxiomsConverter(owlAxiom_set);

        System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
                + role_set.size() + "] role names from [" + formula_list.size() + "] normalized axioms");

        long startTime_1 = System.currentTimeMillis();
        Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(forgetter.Forgetting(role_set, concept_set, formula_list, onto_2));

        System.out.println("ui size = " + uniform_interpolant.size());
        long endTime_1 = System.currentTimeMillis();
        System.out.println("Forgetting Duration = " + (endTime_1 - startTime_1) + " millis");

        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology witness_complete_onto = manager.createOntology(IRI.generateDocumentIRI());
        OWLOntology witness_explicit_onto = manager.createOntology(IRI.generateDocumentIRI());
        OWLOntology witness_implicit_onto = manager.createOntology(IRI.generateDocumentIRI());

        List<Formula> compwitnessList = new ArrayList<>();
        List<Formula> exwitnessList = new ArrayList<>();
        List<Formula> imwitnessList = new ArrayList<>();
        int numc = 0,numi = 0,nume = 0;
        //OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto_1);
        OWLReasoner reasoner = new ElkReasonerFactory().createReasoner(onto_1);

        long startTime_2 = System.currentTimeMillis();

        for (OWLAxiom axiom : uniform_interpolant) {
            if (!reasoner.isEntailed(axiom)) {
                numc++;
                manager.applyChange(new AddAxiom(witness_complete_onto, axiom));

                compwitnessList.addAll(ct.AxiomsConverter(Collections.singleton((OWLLogicalAxiom)axiom)));///
                if (onto_2.getAxioms().contains(axiom)) {
                    nume++;
                    manager.applyChange(new AddAxiom(witness_explicit_onto, axiom));
                    exwitnessList.addAll(ct.AxiomsConverter(Collections.singleton((OWLLogicalAxiom)axiom)));/////
                } else {
                    numi++;
                    manager.applyChange(new AddAxiom(witness_implicit_onto, axiom));
                    imwitnessList.addAll(ct.AxiomsConverter(Collections.singleton((OWLLogicalAxiom)axiom)));/////
                }
            }
        }
        long endTime_2 = System.currentTimeMillis();
        System.out.println("Entailment Duration = " + (endTime_2 - startTime_2) + " millis");
        reasoner.dispose();

        System.out.println("comwitness:" +numc);
        System.out.println("exwitness:" +nume);
        System.out.println("imwitness:" +numi);
        List<List> ans = new ArrayList<>();
        ans.add(compwitnessList);ans.add(exwitnessList);ans.add(imwitnessList);
        return ans;

    }

     */

    public  List<List> getAxiomsShortForm( String path ) throws OWLOntologyCreationException, CloneNotSupportedException {
        Converter ct = new Converter();
        Simplifier pp = new Simplifier();
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology onto_1 = manager.loadOntologyFromOntologyDocument(new File(path));
        List<Formula> formula_list1 = ct.OntologyConverter(onto_1);/////
        Set<OWLClass> c_sig = onto_1.getClassesInSignature();
        Set<OWLObjectProperty> r_sig = onto_1.getObjectPropertiesInSignature();
        Set<AtomicRole > role_set = ct.getRolesfromObjectProperties(r_sig);//////
        Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);////
        List<AtomicRole> roleList = new ArrayList<>(role_set);
        List<AtomicConcept> conceptList = new ArrayList<>(concept_set);
        List<List> ans = new ArrayList<>();
        ans.add(formula_list1);ans.add(roleList);ans.add(conceptList);
        return ans;
    }
    public  List<List> getClause( String path ) throws OWLOntologyCreationException, CloneNotSupportedException {

        Converter ct = new Converter();
        Simplifier pp = new Simplifier();
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        OWLOntology onto_1 = manager.loadOntologyFromOntologyDocument(new File(path));

        //List<Formula> formula_list1 = pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter(onto_1))));
        List<Formula> formula_list1 = ct.OntologyConverter(onto_1);
        Set<OWLClass> c_sig = onto_1.getClassesInSignature();
        Set<OWLObjectProperty> r_sig = onto_1.getObjectPropertiesInSignature();
        Set<AtomicRole > role_set = ct.getRolesfromObjectProperties(r_sig);
        Set<AtomicConcept> concept_set = ct.getConceptsfromClasses(c_sig);
        List<AtomicRole> roleList = new ArrayList<>(role_set);
        List<AtomicConcept> conceptList = new ArrayList<>(concept_set);
        List<List> ans = new ArrayList<>();
        ans.add(formula_list1);ans.add(roleList);ans.add(conceptList);
        return ans;
    }
    public int testint(){
        return 1;
    }
    public  List<List> getforgettingResults(String path, int []forgetConceptIndex,int []forgetRoleIndex) throws Exception {
        List<List> ans = new ArrayList<>();
        INIT();
        Set<AtomicRole> forgetRoleList = new LinkedHashSet<>();
        Set<AtomicConcept> forgetConceptList = new LinkedHashSet<>();
        List<List> DATA = new showData().getClause(path);
        for(int i:forgetConceptIndex){
            AtomicConcept temp = (AtomicConcept) DATA.get(2).get(i);
            forgetConceptList.add((AtomicConcept) temp.clone());
        }
        for(int i:forgetRoleIndex){
            AtomicRole temp = (AtomicRole) DATA.get(1).get(i);
            forgetRoleList.add((AtomicRole) temp.clone());
        }
        Forgetter forget = new Forgetter();
        BackConverter bc = new BackConverter();
        /*
        Converter ct = new Converter();
        List<Formula> AllformulaListClone = new ArrayList<>();
        for(Object i : DATA.get(0)){
            Formula temp = (Formula)i;
            AllformulaListClone.add(temp.clone());
        }

         */
        OWLOntology ontology =   OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(path));
        Set<OWLObjectProperty> roles = new HashSet<>();
        for(AtomicRole r : forgetRoleList){
            roles.add(bc.toOWLObjectProperty(r));
        }
        Set<OWLClass> concepts = new HashSet<>();
        for(AtomicConcept c : forgetConceptList){
            concepts.add(bc.toOWLClass(c));
        }
        List<Formula> results = forget.Forgetting(roles,concepts,ontology,new saveMetrics());
        ans.add( results);
        List<Integer> success = new ArrayList<>();
        success.add(1-Forgetter.isExtra);
        ans.add(success);

        Set<OWLAxiom> result_set = bc.toOWLAxioms(results);
        OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
        OWLOntology ui = manager.createOntology(result_set);
        String dir = path.substring(0,path.lastIndexOf('/')+1);
        System.out.println(dir);
        System.out.println(ui.getLogicalAxiomCount());
        OutputStream os_ui = new FileOutputStream(new File(dir + "ui.owl"));
        manager.saveOntology(ui, os_ui);
        os_ui.close();
        InputStream is = new FileInputStream(dir + "ui.owl");
        System.out.println(dir+"ui.owl");
        String line; // 用来保存每行读取的内容
        BufferedReader reader = new BufferedReader(new InputStreamReader(is));

        StringBuffer sb = new StringBuffer();

        line = reader.readLine(); // 读取第一行
        while (line != null) { // 如果 line 为空说明读完了
            sb.append(line); // 将读到的内容添加到 buffer 中
            sb.append("\n"); // 添加换行符

            line = reader.readLine(); // 读取下一行

        }
        reader.close();
        is.close();
        System.out.println(sb.toString());
        ans.add(Collections.singletonList(sb.toString()));
        return ans;
    }



    public static  void main(String arg[]) throws Exception {

        showData S = new showData();
        List<List> temp = S.getAxiomsShortForm("/Users/liuzhao/nju/ontologyCompare/FINISHED/edam/v1.21.owl");
        for(Object i: temp.get(0)){
            Formula now = (Formula)i;
            System.out.println(now);
        }
        for(Object i: temp.get(1)){
            AtomicRole now = (AtomicRole)i;
            System.out.println(now);
        }
        for(Object i: temp.get(2)){
            AtomicConcept now = (AtomicConcept)i;
            System.out.println(now);
        }
        int []forgetConceptIndex = new int[1];
        forgetConceptIndex[0] = 2;
        int []forgetRoleIndex = new int[0] ;
        List<List> now = S.getforgettingResults("/Users/liuzhao/nju/ontologyCompare/FINISHED/edam/v1.21.owl",forgetConceptIndex,forgetRoleIndex);
        //System.out.println(now.get(2));
        //List<List> nn =new showData().computingLDiff("/Users/liuzhao/nju/ontologyCompare/FINISHED/opbEL/v1.07.owl","/Users/liuzhao/nju/ontologyCompare/FINISHED/opbEL/v1.05.owl");
       // InputStream is = new FileInputStream("/Users/liuzhao/nju/test2.owl");


    }
}
