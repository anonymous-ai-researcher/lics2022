package forgetting;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.text.Normalizer;
import java.util.HashSet;
import java.util.List;
import java.util.*;

import Test.TestForgetting;
import Test.writeFile;
import checkTautology.TautologyChecker;
import checkexistence.EChecker;
import concepts.TopConcept;
import javafx.util.*;
import com.google.common.collect.Sets;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import convertion.Converter;
import elk.*;
import org.semanticweb.HermiT.*;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.*;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.DefinerIntroducer;
import inference.Inferencer;
import inference.simplifier;

import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;
import Test.writeFile.*;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

import javax.swing.event.ListDataEvent;


public class Forgetter {
    public static  int isExtra = 0;


	public Set<OWLAxiom> ForgettingAPI(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception{
    	List<Formula> res = Forgetting(roles,concepts,onto);
    	BackConverter bc = new BackConverter();
    	Set<OWLAxiom> axioms = bc.toOWLAxioms(res);
    	return axioms;
	}

	/**
	 *
	 * @param roles 要遗忘的role
	 * @param concepts 要遗忘的concept
	 * @param onto 这个就是读入的onto不需要，传入之前不需要做任何操作，传入后，需要删除不是ELH的axioms，再形成本体。
	 * @return
	 * @throws Exception
	 */
	public List<Formula> Forgetting(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception {
		DefinerIntroducer di = new DefinerIntroducer();
		SubsetExtractor se = new SubsetExtractor();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		simplifier sp = new simplifier();
		Converter ct = new Converter();
		BackConverter bc = new BackConverter();



		//提取module
		Set<OWLEntity> forgettingSignatures = new HashSet<>();
		forgettingSignatures.addAll(roles);
		forgettingSignatures.addAll(concepts);
		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = sp.extractModule(onto,Sets.difference(onto.getSignature(), forgettingSignatures));
		System.out.println("module size "+moduleOnto_2OnForgettingSig.size());
		//优化：1.defined concepts指的是只出现在equiv或inclusion左边的concept names，对于defined concept A，如果A
		//涉及的axiom只有1个，则直接删掉涉及的axiom， 如果A涉及到的axioms有多个，就先用equiv的右边去替换inclusion中的A，再删除掉equiv
		//2.替换所有的axiom中的 Base name（属于forgettingsignature）为T

		moduleOnto_2OnForgettingSig = sp.eliminateDefinedConceptsAndBasedConcepts(moduleOnto_2OnForgettingSig,concepts);

		//list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
		List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
		//onto =bc.toOWLOntology(formula_list_normalised);

		//做一些不必要的初始化 防止bug
        AtomicConcept.definer_indexInit();
        TestForgetting.isExtra = 0;
        Forgetter.isExtra = 0;

		//初始化reasoner
		System.out.println("hermit begin");
		//OWLReasoner  hermit = new ReasonerFactory().createReasoner(onto);
		OWLReasoner  hermit = new Reasoner(new Configuration(),onto);
		System.out.println("hermit finished");

		//forgetting signature数据结构转换
		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(roles);
		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(concepts);

		System.out.println("The Forgetting Starts:");
		System.out.println("The forgetting task is to eliminate [" + c_sig.size() + "] concept names and ["
				+ r_sig.size() + "] role names from [" + formula_list_normalised.size() + "] normalized axioms");
		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			//List<AtomicRole> r_sig_ordering = ordering2(r_sig,r_sig_list_normalised);

			int i = 1;
			for (AtomicRole role : r_sig) {

				System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				pivot_list_normalised = se.getRoleSubset(role, r_sig_list_normalised);
				if (pivot_list_normalised.isEmpty()) {

				} else {

                    pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);///
                    pivot_list_normalised = inf.combination_R(role, pivot_list_normalised, onto,hermit);

					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			formula_list_normalised.addAll(r_sig_list_normalised);
		}

		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			List<AtomicConcept> c_sig_ordering = sp.ordering(c_sig,c_sig_list_normalised);
			for (AtomicConcept concept : c_sig_ordering) {
			//for (AtomicConcept concept : c_sig) {
				System.out.println("Forgetting Concept [" + j + "] (of "+c_sig_ordering.size()+") = " + concept);
				//System.out.println("Reasoning with "+concept);
				j++;
				pivot_list_normalised = se.getConceptSubset(concept, c_sig_list_normalised);

				if (pivot_list_normalised.isEmpty()) {
					
				} else if (fc.positive(concept, pivot_list_normalised) == 0 ||
						fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(inf.Purify(concept, pivot_list_normalised));

				} else {
                    pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
					pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto,hermit);
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
				c_sig_list_normalised = new ArrayList<>(new HashSet<>(c_sig_list_normalised));


			}

			formula_list_normalised.addAll(c_sig_list_normalised);

		}





		/*
		if (!DefinerIntroducer.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = new ArrayList<>();
			List<Formula> forgetting_Definer_output = new ArrayList<>();
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;
			////this is the case of the cyclic cases, that's why the ACK_A is not re-used. 
			//In case the results of contains this case. report!
			int k = 1;
			do {
				if (DefinerIntroducer.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(forgetting_Definer_output);

					return formula_list_normalised;
				}
				
				definer_set = new LinkedHashSet<>(DefinerIntroducer.definer_set);
				d_sig_list_normalised = se.getConceptSubset(DefinerIntroducer.definer_set, formula_list_normalised);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+DefinerIntroducer.definer_set.size());
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						System.out.println("purify 1");
						List<Formula> temp = inf.Purify(concept, pivot_list_normalised);
						forgetting_Definer_output.addAll(temp);
						for(Formula i : temp){
							System.out.println(i);
						}
						System.out.println("-----------");
						DefinerIntroducer.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						System.out.println("purify 2");
						List<Formula> temp = inf.Purify(concept, pivot_list_normalised);
						forgetting_Definer_output.addAll(temp);
						for(Formula i : temp){
							System.out.println(i);
						}
						System.out.println("-----------");
						DefinerIntroducer.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised, onto);
						forgetting_Definer_output.addAll(pivot_list_normalised);
					}
				}

			} while (true);
			*/

		if (!di.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;
			List<Formula> forgetting_Definer_output = new ArrayList<>();

			////this is the case of the cyclic cases, that's why the ACK_A is not re-used.
			//In case the results of contains this case. report!
			int k = 1;
			int num = 0;

			do {
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);

					return formula_list_normalised;
				}

				definer_set = new LinkedHashSet<>(di.definer_set);

				//List<AtomicConcept>  definer_set_inverse = new ArrayList<>(definer_set.size());
				//List<AtomicConcept> definer_set_ordering = ordering(definer_set,d_sig_list_normalised);
				//for (AtomicConcept concept : definer_set_ordering) {
				for (AtomicConcept concept : definer_set) {
				num++;
					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);

						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);

						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else {
						System.out.println("before introduced " +pivot_list_normalised);
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						System.out.println("after introduced " +pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised ,onto,hermit);
						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}
				if(num > 6000){
					TestForgetting.isExtra = 1;
                    Forgetter.isExtra = 1;
                    System.out.println("There is extra expressivity !");
					break;
				}
			} while (true);


		}
		else{
			System.out.println("DefinersSet is empty!! ");
			System.out.println("Forgetting Successful!");
			System.out.println("===================================================");


		}
		hermit.dispose();
		return formula_list_normalised;
	}
	public static void main(String [] args) throws  Exception {

    	testGhadah();

	}
	public static void testmain()throws  Exception{
		String ontoPath = "/Users/liuzhao/nju/ontologyCompare/FINISHED/edam/v1.21.owl";
		OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
		OWLOntology onto = manager.loadOntologyFromOntologyDocument(new File(ontoPath));

		Set<OWLClass>concepts = onto.getClassesInSignature();
		Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
		List<OWLClass> conceptList = new ArrayList<>(concepts);
		List<OWLObjectProperty>roleList = new ArrayList<>(roles);
		int forgettingroleNumber = 1;
		int forgettingconcpetNumber = 1;
		List<OWLClass> forgettingConcepts = TestForgetting.getSubStringByRadom2(conceptList,forgettingconcpetNumber);
		List<OWLObjectProperty> forgettingRoles = TestForgetting.getSubStringByRadom1(roleList, forgettingroleNumber);
		Forgetter fg = new Forgetter();
		Set<OWLAxiom> ui = fg.ForgettingAPI(new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology uitemp = man.createOntology(ui);

		OutputStream os_ui = new FileOutputStream(new File( "ui.owl"));
		man.saveOntology(uitemp,os_ui);
		System.out.println(uitemp.getLogicalAxiomCount());
	}
	public static void testGhadah()throws Exception{
		String ontoPath = "/Users/liuzhao/Desktop/goslim_mouse.owl";
		OWLOntology prerserve_cig = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File(ontoPath));
		OWLOntology onto = OWLManager.createOWLOntologyManager().loadOntologyFromOntologyDocument(new File("/Users/liuzhao/Desktop/go.owl_denormalised.owl"));
		Set<OWLClass> cig = prerserve_cig.getClassesInSignature();
		Set<OWLClass> forgettingcig = Sets.difference(onto.getClassesInSignature(),cig);
		Set<OWLObjectProperty> roles = new LinkedHashSet<>();
		Forgetter fg = new Forgetter();
		List<Formula> temp = fg.Forgetting(roles,forgettingcig,onto);
		System.out.println(temp.size());
	}
}
