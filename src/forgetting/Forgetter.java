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
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import roles.AtomicRole;
import Test.writeFile.*;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;

import javax.swing.event.ListDataEvent;


public class Forgetter {
    public static  int isExtra = 0;
    public List<AtomicConcept> ordering(Set<AtomicConcept> c_sig,List<Formula> c_sig_list_normalised){
    	List<Formula> now_c_sig_list_normalised = new ArrayList<>(c_sig_list_normalised);
		List<AtomicConcept> now = new ArrayList<>(c_sig);
		FChecker fc = new FChecker();
		Queue<Pair<Integer,AtomicConcept>> Q = new PriorityQueue<>(new queueComparator());
		List<AtomicConcept> ans = new ArrayList<>();
		SubsetExtractor se = new SubsetExtractor();
		int t = 0;
		for(AtomicConcept concept : now){
			int num = 0;
			List<Formula>pivot_list_normalised = se.getConceptSubset(concept, now_c_sig_list_normalised);
			num=fc.positive(concept,pivot_list_normalised);
			num*=fc.negative(concept,pivot_list_normalised);
			Pair<Integer,AtomicConcept> temp= new Pair<>(num,concept);
			Q.add(temp);
			System.out.println(now.size()+" "+t);
			t++;

		}
		while(!Q.isEmpty()){
			Pair<Integer,AtomicConcept> temp=Q.poll();
			System.out.println(temp.getKey());
			ans.add(temp.getValue());
		}
		return ans;

	}
	public List<AtomicRole> ordering2(Set<AtomicRole> c_sig,List<Formula> r_sig_list_normalised){
		List<Formula> now_r_sig_list_normalised = new ArrayList<>(r_sig_list_normalised);
		List<AtomicRole> now = new ArrayList<>(c_sig);
		FChecker fc = new FChecker();
		Queue<Pair<Integer,AtomicRole>> Q = new PriorityQueue<>(new queueComparator2());
		List<AtomicRole> ans = new ArrayList<>();
		SubsetExtractor se = new SubsetExtractor();
		int t = 0;
		for(AtomicRole role : now){
			int num = 0;
			List<Formula>pivot_list_normalised = se.getRoleSubset(role, now_r_sig_list_normalised);
			num=fc.positive(role,pivot_list_normalised);
			num*=fc.negative(role,pivot_list_normalised);
			Pair<Integer,AtomicRole> temp= new Pair<>(num,role);
			Q.add(temp);
			System.out.println(now.size()+" "+t);
			t++;

		}
		while(!Q.isEmpty()){
			Pair<Integer,AtomicRole> temp=Q.poll();
			System.out.println(temp.getKey());
			ans.add(temp.getValue());
		}
		return ans;
	}
	public Set<OWLAxiom> ForgettingAPI(Set<OWLObjectProperty> roles, Set<OWLClass> concepts, OWLOntology onto) throws Exception{
    	Converter ct = new Converter();
    	Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(roles);
    	Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(concepts);
    	List<Formula> formula_list_normalised = ct.OntologyConverter(onto);
    	List<Formula> res = Forgetting(r_sig,c_sig,formula_list_normalised,onto);
    	BackConverter bc = new BackConverter();
    	Set<OWLAxiom> axioms = bc.toOWLAxioms(res);
    	return axioms;
	}
	public List<Formula> Forgetting(Set<AtomicRole> r_sig, Set<AtomicConcept> c_sig,
			List<Formula> formula_list_normalised, OWLOntology onto) throws Exception {
        AtomicConcept.definer_indexInit();
        TestForgetting.isExtra = 0;
        Forgetter.isExtra = 0;
		System.out.println("The Forgetting Starts:");
        OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
        //OWLOntology onto = manager.createOntology(onto2.getAxioms());// it is a copy of onto2
		//OWLOntology onto  = manager.copyOntology(onto2, OntologyCopy.DEEP);
		DefinerIntroducer di = new DefinerIntroducer();
		//Simplifier pp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		BackConverter bc = new BackConverter();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		OWLReasoner      hermit = new ReasonerFactory().createReasoner(onto);

		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, formula_list_normalised);
			List<Formula> pivot_list_normalised = null;
			//List<AtomicRole> r_sig_ordering = ordering2(r_sig,r_sig_list_normalised);
/*
			int nn = 0;
			for(AtomicRole role:r_sig){
				System.out.println(role);
				nn++;
				int positive = 0;
				int negative = 0;
				int equiv = 0;
				for(Formula formula : r_sig_list_normalised){

					if(formula.toString().contains(role.toString())){
						System.out.println(role+" ///  "+formula);
						if(formula instanceof Inclusion){
							if(formula.getSubFormulas().get(0).toString().contains(role.toString())){
								negative++;
							}
							else{
								positive++;
							}
						}


					}
				}
				System.out.println(nn+" "+positive+" "+negative+" "+equiv+"-------------");
				System.out.println(444);
			}

 */


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
			List<AtomicConcept> c_sig_ordering = ordering(c_sig,c_sig_list_normalised);
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
		Set<OWLEntity> tempcig = new LinkedHashSet<>();
		tempcig.addAll(cig);
		Converter ct = new Converter();
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto, ModuleType.BOT);
		Set<OWLAxiom> moduleOnto_2OnForgettingSig = extractor.extract(tempcig);
		Set<OWLLogicalAxiom>moduleOnto_2_OnCommonSig_logical = new HashSet<>();

		for(OWLAxiom axiom : moduleOnto_2OnForgettingSig){
			if(axiom instanceof OWLLogicalAxiom){
				moduleOnto_2_OnCommonSig_logical.add((OWLLogicalAxiom)axiom);
			}
		}
		List<Formula> formula_list = ct.AxiomsConverter(moduleOnto_2_OnCommonSig_logical);
		Set<OWLClass> forgettingcig = Sets.difference(onto.getClassesInSignature(),cig);
		Set<AtomicConcept> concepts = ct.getConceptsfromClasses(forgettingcig);
		Set<AtomicRole> roles = new LinkedHashSet<>();
		Forgetter fg = new Forgetter();
		List<Formula> temp = fg.Forgetting(roles,concepts,formula_list,onto);
		System.out.println(temp.size());
	}
}
class queueComparator implements  Comparator<Pair<Integer,AtomicConcept>>{
	public int compare(Pair<Integer,AtomicConcept> e1, Pair<Integer,AtomicConcept> e2) {
		return e1.getKey() - e2.getKey();//升序
		//return e2.getKey() - e1.getKey();//降序

	}
}
class queueComparator2 implements  Comparator<Pair<Integer,AtomicRole>>{
	public int compare(Pair<Integer,AtomicRole> e1, Pair<Integer,AtomicRole> e2) {
		return e1.getKey() - e2.getKey();//升序
		//return e2.getKey() - e1.getKey();//降序

	}
}