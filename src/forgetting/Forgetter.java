package forgetting;

import java.io.File;
import java.io.FileOutputStream;
import java.io.OutputStream;
import java.text.Normalizer;
import java.util.HashSet;
import java.util.List;
import java.util.*;
import java.lang.Class;
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
import uk.ac.man.cs.lethe.forgetting.*;
import uk.ac.man.cs.lethe.interpolation.IOWLInterpolator;
import uk.ac.man.cs.lethe.interpolation.*;

import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

import javax.swing.event.ListDataEvent;


public class Forgetter {
    public static  int isExtra = 0;


	public Set<OWLAxiom> ForgettingAPI(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception{
    	List<Formula> res = Forgetting(roles,concepts,onto,new saveMetrics());
    	BackConverter bc = new BackConverter();
    	Set<OWLAxiom> axioms = bc.toOWLAxioms(res);

		return axioms;
	}
	/**
	 *这个是CIKM版本的forgetting 不加优化
	 * @param roles 要遗忘的role
	 * @param concepts 要遗忘的concept
	 * @param onto 这个就是读入的onto不需要，传入之前不需要做任何操作，传入后，需要删除不是ELH的axioms，再形成本体。
	 * @return
	 * @throws Exception
	 */
	public List<Formula> ForgettingOldVersion(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception {
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
		//System.out.println("module size "+moduleOnto_2OnForgettingSig.size());

		//list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
		List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
		//onto =bc.toOWLOntology(formula_list_normalised);

		//做一些不必要的初始化 防止bug
		AtomicConcept.definer_indexInit();
		TestForgetting.isExtra = 0;
		Forgetter.isExtra = 0;

		//初始化reasoner
		System.out.println("hermit begin");

		OWLReasoner hermit = null;
		try {


			hermit = new ReasonerFactory().createReasoner(onto);
		}catch (Exception e){
			System.out.println(e);
			return null;
		}
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
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
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
	/**
	 *
	 * @param roles 要遗忘的role
	 * @param concepts 要遗忘的concept
	 * @param onto 这个就是读入的onto不需要，传入之前不需要做任何操作，传入后，需要删除不是ELH的axioms，再形成本体。
	 * @return
	 * @throws Exception
	 */
	public List<Formula> Forgetting(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto,saveMetrics metrics) throws Exception {
		double tempTime1 = System.currentTimeMillis();
		DefinerIntroducer di = new DefinerIntroducer();
		SubsetExtractor se = new SubsetExtractor();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		simplifier sp = new simplifier();
		Converter ct = new Converter();
		int conceptsSize = concepts.size();
		//提取
		Set<OWLEntity> forgettingSignatures = new HashSet<>();
		forgettingSignatures.addAll(roles);
		forgettingSignatures.addAll(concepts);
		Set<OWLLogicalAxiom> moduleOnto_2OnForgettingSig = sp.extractModule(onto,Sets.difference(onto.getSignature(), forgettingSignatures));
		//优化：1.只有1个A = 。。。定义式 删掉 2。 A全是in的 A in B A in C existr.A in B 即在左边并且没有等号的，直接删掉 3。有定义式的 ，用定义式右边的去替换
		//其他地方的A，其他地方的A包括左边和右边的 4. 如果一个concept只出现在右边，全部替换成T
		moduleOnto_2OnForgettingSig = sp.eliminateDefinedConceptsAndBasedConcepts(moduleOnto_2OnForgettingSig,concepts,metrics);

		//list转换 转换过程中会删除掉不是ELH的axiom,同时形成新的onto
		List<Formula> formula_list_normalised = ct.AxiomsConverter(moduleOnto_2OnForgettingSig);
		//onto =bc.toOWLOntology(formula_list_normalised);

		//做一些不必要的初始化 防止bug
        AtomicConcept.definer_indexInit();
        TestForgetting.isExtra = 0;
        Forgetter.isExtra = 0;

		//初始化reasoner
		System.out.println("hermit begin");
		OWLReasoner hermit = null;
		try {


		hermit = new ReasonerFactory().createReasoner(onto);
		}catch (Exception e){
			System.out.println(e);
			return null;
		}
		//OWLReasoner  hermit = new Reasoner(new Configuration(),onto);
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
					//todo cyclic check
					//for(Formula formula : pivot_list_normalised){
					//	Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
					///	if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
					//		System.out.println(formula);
					//		throw new Exception();
					//	}
					//}


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
					System.out.println("Forgetting Successful2!");
					System.out.println("===================================================");
					formula_list_normalised.addAll(d_sig_list_normalised);

					break;
				}

				definer_set = new LinkedHashSet<>(di.definer_set);

				//List<AtomicConcept>  definer_set_inverse = new ArrayList<>(definer_set.size());
				//List<AtomicConcept> definer_set_ordering = ordering(definer_set,d_sig_list_normalised);
				//for (AtomicConcept concept : definer_set_ordering) {
				for (AtomicConcept concept : definer_set) {
					num++;
					if(num > 6000) break;
					System.out.println("Forgetting Definer [" + k + "] = " + concept +" definer_set size :"+di.definer_set.size());
					k++;
					pivot_list_normalised = se.getConceptSubset(concept, d_sig_list_normalised);
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
						/*
						//todo cyclic check
						for(Formula formula : ans){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */
						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {

						List<Formula> ans = inf.Purify(concept, pivot_list_normalised);
						/*
						//todo cyclic check
						for(Formula formula : ans){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */


						d_sig_list_normalised.addAll(ans);
						di.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = inf.combination_A(concept, pivot_list_normalised ,onto,hermit);
						/*
						//todo cyclic check
						for(Formula formula : pivot_list_normalised){
							Set<AtomicConcept> common = Sets.intersection(formula.getSubFormulas().get(0).get_c_sig(),formula.getSubFormulas().get(1).get_c_sig());
							if((Sets.intersection(common,c_sig).size()!=0|| Sets.intersection(common,di.definer_set).size()!=0)){
								num = 10000;
								//throw new Exception();
							}
						}

						 */


						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}
				if(num > 6000){
					metrics.isExtra = 1;
					TestForgetting.isExtra = 1;
                    Forgetter.isExtra = 1;
                    System.out.println("There is extra expressivity !");
					break;
				}
			} while (true);


		}
		else{
			metrics.success = 1;
			System.out.println("DefinersSet is empty!! ");
			System.out.println("Forgetting Successful!");
			System.out.println("===================================================");


		}
		hermit.dispose();
		//调试 可以删除
		double tempTime2 = System.currentTimeMillis();
		int optSum = metrics.optimizeNum1+metrics.optimizeNum4+metrics.optimizeNum3+metrics.optimizeNum2;
		System.out.println("message "+conceptsSize+"\t"+(tempTime2-tempTime1)+"\t"+(optSum*1.0/conceptsSize));
		//return new ArrayList<>(new HashSet<>(formula_list_normalised));
		return formula_list_normalised;
	}
	public static void main(String [] args) throws  Exception {

		//testmain();
		String ontoPath = "/Users/liuzhao/Desktop/Untitled2.owl";
		OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
		OWLOntology onto = manager.loadOntologyFromOntologyDocument(new File(ontoPath));
		Set<OWLEntity> concepts = new HashSet<>();
		for(OWLEntity temp : onto.getSignature()){
			if(temp.toString().contains("B") || temp.toString().contains("F")) concepts.add(temp);;
		}
		System.out.println(concepts);
		AlchTBoxForgetter now = new AlchTBoxForgetter();
		AlchTBoxInterpolator te = new AlchTBoxInterpolator();
		//OWLOntology ans = te.uniformInterpolant(onto,concepts);
		OWLOntology ans = now.forget(onto,concepts);
		System.out.println(ans.getLogicalAxioms());
	}
	public static void testmain()throws  Exception{
		String ontoPath = "/NCBOcrawler/GO/go1802.owl";
		OWLOntologyManager manager =  OWLManager.createOWLOntologyManager();
		OWLOntology onto = manager.loadOntologyFromOntologyDocument(new File(ontoPath));

		Set<OWLClass>concepts = onto.getClassesInSignature();
		Set<OWLObjectProperty>roles = onto.getObjectPropertiesInSignature();
		List<OWLClass> conceptList = new ArrayList<>(concepts);
		List<OWLObjectProperty>roleList = new ArrayList<>(roles);
		int forgettingroleNumber = 0;
		int forgettingconcpetNumber = 10;
		List<OWLClass> forgettingConcepts = TestForgetting.getSubStringByRadom2(conceptList,forgettingconcpetNumber);
		List<OWLObjectProperty> forgettingRoles = TestForgetting.getSubStringByRadom1(roleList, forgettingroleNumber);
		Forgetter fg = new Forgetter();
		Set<OWLAxiom> ui = fg.ForgettingAPI(new HashSet<>(forgettingRoles),new HashSet<>(forgettingConcepts),onto);
		OWLOntologyManager man = OWLManager.createOWLOntologyManager();
		OWLOntology uitemp = man.createOntology(ui);

		OutputStream os_ui = new FileOutputStream(new File( "ui11.owl"));
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
		List<Formula> temp = fg.Forgetting(roles,forgettingcig,onto,new saveMetrics());
		System.out.println(temp.size());
	}
}
