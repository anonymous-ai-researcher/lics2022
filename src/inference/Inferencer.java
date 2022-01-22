package inference;

import java.io.File;
import java.text.Normalizer;
import java.util.*;

import checkTautology.TautologyChecker;
import connectives.Equivalence;
import elk.elkEntailment;
import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner;
//import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
//import org.semanticweb.owlapi.reasoner.InferenceType;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
//import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import BackTrack.*;
import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.TopConcept;
import roles.AtomicRole;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import convertion.BackConverter;
import formula.Formula;

public class Inferencer {

	//private OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	//private OWLDataFactory factory = manager.getOWLDataFactory();
	
	//LoadButtonListener lbl = new LoadButtonListener();
	
	//OWLOntology onto = lbl.ontology;
	public Inferencer() {

	}
	/*
	public void check(Formula now,Formula pe1,Formula pe2,int tag,OWLOntology onto) throws Exception{
		OWLReasoner reasoner =  new ElkReasonerFactory().createReasoner(onto);
		BackConverter bc = new BackConverter();
		OWLAxiom axiom = bc.toOWLAxiom(now);
		if(!axiom.toString().contains("finer") && !elkEntailment.entailed(reasoner,axiom) ){
			System.out.println("result: " +now);
			System.out.println("pe1: "+ pe1);

			System.out.println("pe2: "+ pe2);
			System.out.println("tag: "+tag);
			throw new Exception("I find it !");
		}
		reasoner.dispose();



	}
	*
	 */

	public List<Formula> combination_A(AtomicConcept concept, List<Formula> formula_list, OWLOntology onto,OWLReasoner  reasoner) // List has two elements, the result list after forgetting and the number of the usage of each rule
			throws Exception {
		//OWLReasoner reasoner = new ElkReasonerFactory().createReasoner(onto);
		BackConverter bc = new BackConverter();
		TautologyChecker tc = new TautologyChecker();
		

		List<Formula> output_list = new ArrayList<>();
		/*
		List<Formula> positive_star_premises = new ArrayList<>(); // C in A   1
		List<Formula> positive_exists_premises = new ArrayList<>(); //  C in exist r. A   2
		List<Formula> positive_exists_and_premises = new ArrayList<>(); //  C in exist r. (A and B)   3
		List<Formula> negative_star_premises = new ArrayList<>(); // A in G  4
		List<Formula> negative_star_and_premises = new ArrayList<>(); // A and F in G  5
		List<Formula> negative_exists_premises = new ArrayList<>(); //  exist r. A in G   6
		List<Formula> negative_star_and_exists_premises = new ArrayList<>(); // exists r.A and F in G   7
		List<Formula> negative_exists_and_premises = new ArrayList<>(); //  exist r. (A and D) in G   8
		List<Formula> negative_star_and_exists_and_premises = new ArrayList<>(); //  exist r. (A and D) and F in G   9
		 */
		Set<Formula> positive_star_premises = new LinkedHashSet<>(); // C in A   1
		Set<Formula> positive_exists_premises = new LinkedHashSet<>(); //  C in exist r. A   2
		Set<Formula> positive_exists_and_premises = new LinkedHashSet<>(); //  C in exist r. (A and B)   3
		Set<Formula> negative_star_premises = new LinkedHashSet<>(); // A in G  4
		Set<Formula> negative_star_and_premises = new LinkedHashSet<>(); // A and F in G  5
		Set<Formula> negative_exists_premises = new LinkedHashSet<>(); //  exist r. A in G   6
		Set<Formula> negative_star_and_exists_premises = new LinkedHashSet<>(); // exists r.A and F in G   7
		Set<Formula> negative_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) in G   8
		Set<Formula> negative_star_and_exists_and_premises = new LinkedHashSet<>(); //  exist r. (A and D) and F in G   9

		EChecker ec = new EChecker();

		for (Formula formula : formula_list) {
			if(tc.isTautology(formula)) continue;
			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);
			if (!ec.isPresent(concept, formula)) {
				output_list.add(formula);

			} else if (subsumer.equals(concept)) {
				positive_star_premises.add(formula);
	
			} else if (subsumer instanceof Exists &&
					ec.isPresent(concept, subsumer)) {

				if(subsumer.getSubFormulas().get(1).equals(concept))positive_exists_premises.add(formula);
				else positive_exists_and_premises.add(formula);
	
			} else if (subsumee.equals(concept)) {
				negative_star_premises.add(formula);

			} else if (subsumee instanceof And) {
				if (subsumee.getSubformulae().contains(concept)) { ////// changed

					negative_star_and_premises.add(formula);
				} else {
					for(Formula f : subsumee.getSubformulae()){
						if(ec.isPresent(concept,f)){

							if(f.getSubFormulas().get(1).equals(concept)){
								negative_star_and_exists_premises.add(formula);
							}
							else{
								negative_star_and_exists_and_premises.add(formula);
							}
							break;
						}
					}
				}
				
			} else if (subsumee instanceof Exists) {
				if(subsumee.getSubFormulas().get(1).equals(concept)) negative_exists_premises.add(formula);
				else negative_exists_and_premises.add(formula);

			} else {

				throw new Exception("Damn! Error!");
			}
		}
		/*
		System.out.println("1  "+ positive_star_premises.size());
		System.out.println("1  "+ positive_exists_premises.size());

		System.out.println("1  "+ positive_exists_and_premises.size());

		System.out.println("1  "+ negative_star_premises.size());

		System.out.println("1  "+ negative_star_and_premises.size());
		System.out.println("1  "+ negative_exists_premises.size());
		System.out.println("1  "+ negative_star_and_exists_premises.size());
		System.out.println("1  "+ negative_exists_and_premises.size());
		System.out.println("1  "+ negative_star_and_exists_and_premises.size());

		System.out.println(concept);

		 */



		//1
		int time  = 0;
		for (Formula ps_premise : positive_star_premises) {
			time++;

			Formula subsumee = ps_premise.getSubFormulas().get(0);
			for (Formula ns_premise : negative_star_premises) {
				Formula temp = AckermannReplace(concept, ns_premise, subsumee);
				if( !tc.isTautology(temp)) output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),ns_premise.clone(),3);
			}

			for (Formula nsa_premise : negative_star_and_premises) {
				Formula temp = AckermannReplace(concept, nsa_premise, subsumee);
				if(!tc.isTautology(temp)) output_list.add(temp);
				//System.out.println(concept+" "+ps_premise +" "+negative_star_and_premises.size()+" "+positive_star_premises.size() +" "+ time);
				//System.out.println(nsa_premise);

				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),nsa_premise.clone(),4);
			}


			for (Formula ne_premise : negative_exists_premises) {
				Formula temp = AckermannReplace(concept, ne_premise, subsumee);
				if(!tc.isTautology(temp)) output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),ne_premise.clone(),5);

			}
			for(Formula nea_premise : negative_exists_and_premises){
				Formula temp = AckermannReplace(concept, nea_premise, subsumee);
				if(!tc.isTautology(temp)) output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),nea_premise.clone(),5);
			}
			for(Formula nsae_premise :negative_star_and_exists_premises){
				Formula temp = AckermannReplace(concept,nsae_premise,subsumee);
				if(!tc.isTautology(temp)) output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),nsae_premise.clone(),5);
			}
			for(Formula nsaea_premise: negative_star_and_exists_and_premises){
				Formula temp = AckermannReplace(concept,nsaea_premise,subsumee);
				if(!tc.isTautology(temp)) output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),nsaea_premise.clone(),5);
			}
		}

		//2
		/*
		OWLReasoner reasoner = null;
		if(positive_exists_premises.size()!=0&&(negative_star_and_premises.size()!=0||negative_exists_premises.size()!=0||negative_exists_and_premises.size()
		!=0||negative_star_and_exists_premises.size()!=0 || negative_star_and_exists_and_premises.size()!=0)){
			reasoner = new ElkReasonerFactory().createReasoner(onto);
		}
		else if(positive_exists_and_premises.size()!=0&&(negative_star_and_premises.size()!=0||negative_exists_premises.size()!=0||negative_exists_and_premises.size()
				!=0||negative_star_and_exists_premises.size()!=0 || negative_star_and_exists_and_premises.size()!=0)){
			reasoner = new ElkReasonerFactory().createReasoner(onto);
		}

		 */

		//OWLReasoner reasoner = new Reasoner(new Configuration(),onto);

		for (Formula pe_premise : positive_exists_premises) {


			int tag = 0;
			//2 4
			if (!negative_star_premises.isEmpty()) {
				tag = 1;
				Formula temp = null;
				if(negative_star_premises.size()>1) {
					Set<Formula> and = new LinkedHashSet<>();
					for (Formula ns_premise : negative_star_premises) {

						and.add(ns_premise.getSubFormulas().get(1));
					}
					Formula ands = And.getAnd(and);



					temp = AckermannReplace(concept, pe_premise, ands);
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),And,7);
				}
				else{
					temp = AckermannReplace(concept, pe_premise, new ArrayList<>(negative_star_premises).get(0).getSubFormulas().get(1));
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),new ArrayList<>(negative_star_premises).get(0).getSubFormulas().get(1),7);
				}
				if(!tc.isTautology(temp)) output_list.add(temp);

			}

			//if(negative_star_and_premises.size()+negative_exists_premises.size()
			//		+negative_star_and_exists_premises.size()+negative_exists_and_premises.size()+negative_star_and_exists_and_premises.size()==0) continue;
			//2 5

			for(Formula nsa_premise :negative_star_and_premises){
				Set<Formula> exceptConcept = new LinkedHashSet<>(); //F
				for(Formula  i: nsa_premise.getSubFormulas().get(0).getSubformulae()){
					if(!ec.isPresent(concept,i)){
						exceptConcept.add(i);
					}
				}
				Formula and =  And.getAnd(exceptConcept);
				Formula nowCheck = new Inclusion(TopConcept.getInstance(),and);
				if(elkEntailment.entailed(reasoner,bc.toOWLSubClassOfAxiom(nowCheck),2)){
					tag = 1;
					Formula temp = new Inclusion(pe_premise.getSubFormulas().get(0),new Exists(pe_premise.getSubFormulas().get(1).
							getSubFormulas().get(0),nsa_premise.getSubFormulas().get(1)));
					if(!tc.isTautology(temp)) output_list.add(temp);

					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),nsa_premise.clone(),7);
				}

			}
			// 2 6
			for(Formula ne_premise :negative_exists_premises){

				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pe_premise.getSubFormulas().get(1).getSubFormulas().get(0),
						ne_premise.getSubFormulas().get(0).getSubFormulas().get(0))),2)){
					tag = 1;
					Formula temp = new Inclusion(pe_premise.getSubFormulas().get(0),ne_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),ne_premise.clone(),7);
				}
			}
			//2 7
			for(Formula nsae_premise:negative_star_and_exists_premises){
				Formula containConcept = null;
				Set<Formula> exceptConcept = new LinkedHashSet<>();//F
				for(Formula i : nsae_premise.getSubFormulas().get(0).getSubformulae()){
					if(ec.isPresent(concept,i)){
						containConcept = i;

					}
					else{
						exceptConcept.add(i);
					}
				}
				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pe_premise.getSubFormulas().get(1).getSubFormulas().get(0),
						containConcept.getSubFormulas().get(0))),2)){
					tag = 1;
					Formula pe_premise_left=  pe_premise.getSubFormulas().get(0);
					if(pe_premise_left instanceof And) exceptConcept.addAll(pe_premise_left.getSubformulae());  // 防止 [A and B, C] 出现
					else exceptConcept.add(pe_premise_left);
					Formula and =  And.getAnd(exceptConcept);
					Formula temp = new Inclusion(and,nsae_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),nsae_premise.clone(),7);
				}
			}
			//2 8
			for(Formula nea_premise :negative_exists_and_premises){
				Set<Formula> exceptConcept = new LinkedHashSet<>();//D

				for(Formula i : nea_premise.getSubFormulas().get(0).getSubFormulas().get(1).getSubformulae()){
					if(!ec.isPresent(concept,i)){
						exceptConcept.add(i);

					}

				}
				Formula and =  And.getAnd(exceptConcept);
				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(TopConcept.getInstance(),and)),2) &&
				elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pe_premise.getSubFormulas().get(1).getSubFormulas().get(0),
						nea_premise.getSubFormulas().get(0).getSubFormulas().get(0))),2)){
					tag = 1;
					Formula temp = new Inclusion(pe_premise.getSubFormulas().get(0),nea_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),nea_premise.clone(),7);

				}

			}
			//2 9
			for(Formula nsaea_premise:negative_star_and_exists_and_premises){
				Formula containConcept = null;
				Set<Formula> exceptConcept = new LinkedHashSet<>(); //F
				for(Formula i : nsaea_premise.getSubFormulas().get(0).getSubformulae()){
					if(ec.isPresent(concept,i)){
						containConcept = i;

					}
					else{
						exceptConcept.add(i);
					}
				}
				Formula s = containConcept.getSubFormulas().get(0);
				AtomicRole role = (AtomicRole)s;
				Set<Formula>exceptConcept2 = new LinkedHashSet<>(); //D
				for(Formula i:containConcept.getSubFormulas().get(1).getSubformulae()){
					if(!ec.isPresent(concept,i)){
						exceptConcept2.add(i);
					}
				}
				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(TopConcept.getInstance(), And.getAnd(exceptConcept2))),2) && elkEntailment.entailed(reasoner,
						bc.toOWLAxiom(new Inclusion(pe_premise.getSubFormulas().get(1).getSubFormulas().get(0),role)),2)){
					tag = 1;
					Formula pe_premise_left=  pe_premise.getSubFormulas().get(0);
					if(pe_premise_left instanceof And) exceptConcept.addAll(pe_premise_left.getSubformulae());  // 防止 [A and B, C] 出现
					else exceptConcept.add(pe_premise_left);
					Formula temp = new Inclusion( And.getAnd(exceptConcept),nsaea_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pe_premise.clone(),nsaea_premise.clone(),7);
				}

			}
			if(tag == 0){
				Formula temp2 = AckermannReplace(concept, pe_premise, TopConcept.getInstance());
				if(!tc.isTautology(temp2)) output_list.add(temp2);
				//BackTrack.addFatherHash(temp2.clone(),pe_premise.clone(),6);
			}



		}

		//3

		for(Formula pea_premise :positive_exists_and_premises){

			int tag = 0;
			// 3 4
			if (!negative_star_premises.isEmpty()) {
				tag = 1;
				Formula temp = null;
				if(negative_star_premises.size()>1) {
					Set<Formula> and = new LinkedHashSet<>();

					for (Formula ns_premise : negative_star_premises) {
						and.add(ns_premise.getSubFormulas().get(1));
					}
					Formula ands =  And.getAnd(and);
					temp = AckermannReplace(concept, pea_premise, ands);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),And.clone(),7);

				}
				else{
					temp = AckermannReplace(concept, pea_premise, new ArrayList<>(negative_star_premises).get(0).getSubFormulas().get(1));
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),new ArrayList<>(negative_star_premises).get(0).getSubFormulas().get(1),7);

				}
				if(!tc.isTautology(temp)) output_list.add(temp);
			}

			//3 5
			for(Formula nsa_premise :negative_star_and_premises){
				Set<Formula> exceptConcept = new LinkedHashSet<>();//F
				for(Formula  i: nsa_premise.getSubFormulas().get(0).getSubformulae()){
					if(!ec.isPresent(concept,i))
						exceptConcept.add(i);

				}
				Formula and =  And.getAnd(exceptConcept);
				Set<Formula> exceptConcept2 = new LinkedHashSet<>();//B
				for(Formula i : pea_premise.getSubFormulas().get(1).getSubFormulas().get(1).getSubformulae()){
					if(!i.equals(concept)) exceptConcept2.add(i);
				}
				Formula and2 =  And.getAnd(exceptConcept2);
				Formula nowCheck = new Inclusion(and2,and);
				if(elkEntailment.entailed(reasoner,bc.toOWLSubClassOfAxiom(nowCheck),2)){
					tag = 1;
					/*
					Formula temp = new Inclusion(pea_premise.getSubFormulas().get(0),new Exists(pea_premise.getSubFormulas().get(1).
							getSubFormulas().get(0),nsa_premise.getSubFormulas().get(1)));

					 */
					if(nsa_premise.getSubFormulas().get(1) instanceof And)
						exceptConcept2.addAll(((And)nsa_premise.getSubFormulas().get(1)).getSubformulae());//todo
					else exceptConcept2.add(nsa_premise.getSubFormulas().get(1));//todo
					Formula temp = new Inclusion(pea_premise.getSubFormulas().get(0),new Exists(pea_premise.getSubFormulas().get(1).
							getSubFormulas().get(0),And.getAnd(exceptConcept2)));//todo

					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),nsa_premise.clone(),7);
				}
			}
			//3 6
			for(Formula ne_premise:negative_exists_premises){

				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pea_premise.getSubFormulas().get(1),
						ne_premise.getSubFormulas().get(0))),2)){
					tag = 1;
					Formula temp = new Inclusion(pea_premise.getSubFormulas().get(0),ne_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),ne_premise.clone(),7);
				}
			}
			//3 7
			for(Formula nsae_premise :negative_star_and_exists_premises){
				Formula containConcept = null;
				Set<Formula> exceptConcept = new LinkedHashSet<>();//F
				for(Formula i : nsae_premise.getSubFormulas().get(0).getSubformulae()){

					if(ec.isPresent(concept,i)){
						containConcept = i;
					}
					else exceptConcept.add(i);
				}
				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pea_premise.getSubFormulas().get(1),
						containConcept)),2)){
					tag = 1;
					Formula pe_premise_left=  pea_premise.getSubFormulas().get(0);
					if(pe_premise_left instanceof And) exceptConcept.addAll(pe_premise_left.getSubformulae());  // 防止 [A and B, C] 出现
					else exceptConcept.add(pe_premise_left);
					Formula and =  And.getAnd(exceptConcept);
					Formula temp = new Inclusion(and,nsae_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),nsae_premise.clone(),7);
				}
			}
			//3 8
			for(Formula nea_premise:negative_exists_and_premises){
				Set<Formula> exceptConcept1 = new LinkedHashSet<>();//D
				for(Formula i : nea_premise.getSubFormulas().get(0).getSubFormulas().get(1).getSubformulae()){
					if(!i.equals(concept)){
						exceptConcept1.add(i);
					}
				}
				Set<Formula> exceptConcept2 = new LinkedHashSet<>();//B
				for(Formula i: pea_premise.getSubFormulas().get(1).getSubFormulas().get(1).getSubformulae()){
					if(!i.equals(concept)){
						exceptConcept2.add(i);
					}
				}

				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion( And.getAnd(exceptConcept2), And.getAnd(exceptConcept1))),2) &&
				elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pea_premise.getSubFormulas().get(1).getSubFormulas().get(0),nea_premise.getSubFormulas().get(0).getSubFormulas().get(0))),2)){
					tag = 1;
					Formula temp = new Inclusion(pea_premise.getSubFormulas().get(0),nea_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),nea_premise.clone(),7);

				}
			}
			//3 9
			for(Formula nsaea_premise:negative_star_and_exists_and_premises){
				Set<Formula> exceptConcept2 = new LinkedHashSet<>();  //B
				for(Formula i: pea_premise.getSubFormulas().get(1).getSubFormulas().get(1).getSubformulae()){
					if(!i.equals(concept)){
						exceptConcept2.add(i);
					}
				}

				Formula containConcept = null;
				Set<Formula> exceptConcept = new LinkedHashSet<>(); //F
				for(Formula i : nsaea_premise.getSubFormulas().get(0).getSubformulae()){

					if(ec.isPresent(concept,i)){
						containConcept = i;

					}
					else{
						exceptConcept.add(i);
					}
				}

				Formula s = containConcept.getSubFormulas().get(0);
				AtomicRole role = (AtomicRole)s; //s

				Set<Formula>exceptConcept3 = new LinkedHashSet<>();  //D
				for(Formula i:containConcept.getSubFormulas().get(1).getSubformulae()){
					if(!i.equals(concept)){
						exceptConcept3.add(i);
					}
				}

				if(elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion( And.getAnd(exceptConcept2), And.getAnd(exceptConcept3))),2) &&
				   elkEntailment.entailed(reasoner,bc.toOWLAxiom(new Inclusion(pea_premise.getSubFormulas().get(1).getSubFormulas().get(0),role)),2)){
					tag = 1;
					Formula pe_premise_left=  pea_premise.getSubFormulas().get(0);
					if(pe_premise_left instanceof And) exceptConcept.addAll(pe_premise_left.getSubformulae());  // 防止 [A and B, C] 出现
					else exceptConcept.add(pe_premise_left);
					Formula temp = new Inclusion( And.getAnd(exceptConcept),nsaea_premise.getSubFormulas().get(1));
					if(!tc.isTautology(temp)) output_list.add(temp);
					//BackTrack.addFatherHash(temp.clone(),pea_premise.clone(),nsaea_premise.clone(),7);
				}


			}
			if(tag == 0){
				Formula temp2 = AckermannReplace(concept, pea_premise, TopConcept.getInstance());
				if(!tc.isTautology(temp2)) output_list.add(temp2);
				//BackTrack.addFatherHash(temp2.clone(),pea_premise.clone(),6);
			}

		}
		//if(!(reasoner == null))
		//	reasoner.dispose();
		//System.out.println("The output list of Ackermann_A: " + output_list);
		return output_list;
	}
	
	public List<Formula> combination_R(AtomicRole role, List<Formula> formula_list, OWLOntology onto,OWLReasoner reasoner)
			throws Exception {
		
		TautologyChecker tc = new TautologyChecker();
		//List<Formula> output_list = new ArrayList<>();
		Set<Formula>output_list = new LinkedHashSet<>();
		// C or A
		List<Formula> positive_star_premises = new ArrayList<>();
		// C or exists r.A
		List<Formula> positive_exists_premises = new ArrayList<>();
		// C or exists r.(A or B)
		List<Formula> negative_star_premises = new ArrayList<>();
		// C or exists r.~A
		List<Formula> negative_exists_premises = new ArrayList<>();
		// C or exists r.(~A or B)

		EChecker ec = new EChecker();
		BackConverter bc = new BackConverter();
		//OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto);

		//reasoner.precomputeInferences(InferenceType.CLASS_HIERARCHY);

		for (Formula formula : formula_list) {
			if(tc.isTautology(formula)) continue;
			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);

				if (!ec.isPresent(role, formula)) {
				output_list.add(formula);

			} else if (subsumer.equals(role)) {
				positive_star_premises.add(formula);
	
			} else if (subsumee.equals(role)) {
				negative_star_premises.add(formula);

			} else if (ec.isPresent(role, subsumer)) {
				positive_exists_premises.add(formula);
	
			} else {
				negative_exists_premises.add(formula);
			}
		}

		System.out.println("2  "+ positive_star_premises.size());
		System.out.println("2  "+ negative_star_premises.size());

		System.out.println("2  "+ positive_exists_premises.size());

		System.out.println("2  "+ negative_exists_premises.size());





		//Case I 对应论文的f e
		for (Formula ps_premise : positive_star_premises) {
			Formula subsumee = ps_premise.getSubFormulas().get(0);
			for (Formula ns_premise : negative_star_premises) {
				Formula temp = AckermannReplace(role, ns_premise, subsumee);
				if(!tc.isTautology(temp))
					output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),ns_premise.clone(),8);
			}
			for (Formula ne_premise : negative_exists_premises) {
				Formula temp = AckermannReplace(role, ne_premise, subsumee);
				if(!tc.isTautology(temp))
					output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ps_premise.clone(),ne_premise.clone(),9);
			}
		}
		// Case II g
		for (Formula ns_premise : negative_star_premises) {
			Formula subsumer = ns_premise.getSubFormulas().get(1);
			for (Formula pe_premise : positive_exists_premises) {
				Formula temp = AckermannReplace(role, pe_premise, subsumer);
				if(!tc.isTautology(temp))
					output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),ns_premise.clone(),pe_premise.clone(),10);
			}
		}
		// Case III h
		int tempi = 0, tempj = 0;

		for (Formula pe_premise : positive_exists_premises) {
			tempi++;
			tempj = 0;
			Formula pe_subsumee = pe_premise.getSubFormulas().get(0);
			Formula pe_subsumer = pe_premise.getSubFormulas().get(1);
			Formula pe_subsumer_filler = pe_subsumer.getSubFormulas().get(1);//D
			for (Formula ne_premise : negative_exists_premises) {
				tempj++;
				Formula ne_subsumee = ne_premise.getSubFormulas().get(0);
				Formula ne_subsumer = ne_premise.getSubFormulas().get(1);
				Formula ne_subsumee_filler = null;//表示  f and exist r.E in C 中的 E
				Formula stored_conjunct = null;// exist r.E
				if (ne_subsumee instanceof Exists) {
					ne_subsumee_filler = ne_subsumee.getSubFormulas().get(1);
				} else {
					Set<Formula> conjunct_set = ne_subsumee.getSubformulae();
					for (Formula conjunct : conjunct_set) {

						if (ec.isPresent(role, conjunct)) {
							ne_subsumee_filler = conjunct.getSubFormulas().get(1);
							stored_conjunct = conjunct;
							break;
						}
					}
				}

				Formula inclusion = new Inclusion(pe_subsumer_filler, ne_subsumee_filler);
				OWLAxiom axiom = bc.toOWLAxiom(inclusion);
				if (elkEntailment.entailed(reasoner, axiom, 2)) {
				//if (elkEntailment.hasChecked_OnO2.containsKey(axiom) && elkEntailment.entailed(reasoner, axiom, 2)) {

					Formula new_inclusion = null;
					if (ne_subsumee instanceof Exists) {
						new_inclusion = new Inclusion(pe_subsumee, ne_subsumer);
					} else {

						Set<Formula> new_conjunct_set = new LinkedHashSet<>(ne_subsumee.getSubformulae());
						new_conjunct_set.remove(stored_conjunct);
						new_conjunct_set.add(pe_subsumee);
						Formula new_subsumee =  And.getAnd(new_conjunct_set);
						new_inclusion = new Inclusion(new_subsumee, ne_subsumer);


					}
					if (!tc.isTautology(new_inclusion)) output_list.add(new_inclusion);
					//BackTrack.addFatherHash(new_inclusion.clone(),pe_premise.clone(),ne_premise.clone(),11);
				}


/*
					if (pe_subsumer_filler.equals(ne_subsumee_filler)) {
						Formula new_inclusion = null;
						if (ne_subsumee instanceof Exists) {
							new_inclusion = new Inclusion(pe_subsumee, ne_subsumer);
						} else {
							Set<Formula> new_conjunct_set = new HashSet<>(ne_subsumee.getSubformulae());
							new_conjunct_set.remove(stored_conjunct);
							new_conjunct_set.add(pe_subsumee);
							if (new_conjunct_set.contains(ne_subsumer)) {
								//System.out.println("Bingo 3!");
								break;
							} else {
								Formula new_subsumee = new And(new_conjunct_set);
								new_inclusion = new Inclusion(new_subsumee, ne_subsumer);
							}
						}
						//System.out.println("Looking forward = " + new_inclusion);
						//System.out.println("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
						output_list.add(new_inclusion);

					} else {
						Formula inclusion = new Inclusion(pe_subsumer_filler, ne_subsumee_filler);
						OWLAxiom axiom = bc.toOWLSubClassOfAxiom(inclusion);
						// System.out.println("axiom before = " + axiom);

						if (elkEntailment.hasChecked_OnO2.containsKey(axiom) &&elkEntailment.entailed(reasoner, axiom, 2)) {
							Formula new_inclusion = null;
							if (ne_subsumee instanceof Exists) {
								new_inclusion = new Inclusion(pe_subsumee, ne_subsumer);
							} else {
								Set<Formula> new_conjunct_set = new HashSet<>(ne_subsumee.getSubformulae());
								new_conjunct_set.remove(stored_conjunct);
								new_conjunct_set.add(pe_subsumee);
								if (new_conjunct_set.contains(ne_subsumer)) {
									//System.out.println("Bingo 4!");
									break;
								} else {
									Formula new_subsumee = new And(new_conjunct_set);
									new_inclusion = new Inclusion(new_subsumee, ne_subsumer);
								}
							}
							//System.out.println("Looking backward = " + new_inclusion);
							//System.out.println("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx");
							output_list.add(new_inclusion);
						}

					}
*/
				}
				//System.out.println(" "+"size :" +positive_exists_premises.size()+" "+" "+negative_exists_premises.size()+" "+tempi+" "+output_list.size());

		}

		return new ArrayList<>(output_list);
	}
	

	public List<Formula> Purify(AtomicConcept concept, List<Formula> input_list)
			throws Exception {
		TautologyChecker tc = new TautologyChecker();
		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				//output_list.add(formula);


			} else {
				Formula temp = Purify(concept, formula);
				if(!tc.isTautology(temp))
					output_list.add(temp);
				//BackTrack.addFatherHash(temp.clone(),formula.clone(),12);

			}
		}

		return output_list;
	}

	public Formula AckermannReplace(AtomicRole role, Formula toBeReplaced, Formula definition) {
		if(!toBeReplaced.toString().contains(role.toString())) return toBeReplaced;
		if (toBeReplaced instanceof AtomicConcept) {
			//return new AtomicConcept(toBeReplaced.getText());
			return  toBeReplaced;

		} else if (toBeReplaced instanceof AtomicRole) {
			//return toBeReplaced.equals(role) ? definition : new AtomicRole(toBeReplaced.getText());
			return toBeReplaced.equals(role) ? definition : toBeReplaced;

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Inclusion) {
			return new Inclusion(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if(toBeReplaced instanceof Equivalence){
			Formula t1 = AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition);
			Formula t2 = AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition);
			return new Equivalence(t1, t2);
		}else if (toBeReplaced instanceof And) {
			Set<Formula> conjunct_list = toBeReplaced.getSubformulae();
			Set<Formula> conjunct_set = new LinkedHashSet<>();
			for (Formula conjunct : conjunct_list) {
				Formula temp = AckermannReplace(role, conjunct, definition);
				if(temp instanceof And) {

					//System.out.println(role+ " "+toBeReplaced+" "+definition);
					conjunct_set.addAll(temp.getSubformulae()); //gaile TODO
					//System.out.println("I find this bug2");

				}
				else conjunct_set.add(temp);
			}
			return  And.getAnd(conjunct_set);

		}

		return toBeReplaced;
	}
	
	public Formula AckermannReplace(AtomicConcept concept, Formula toBeReplaced, Formula definition) {
		if(!toBeReplaced.toString().contains(concept.toString())) return toBeReplaced;

		if (toBeReplaced instanceof AtomicConcept) {
			//System.out.println(1);
			//return toBeReplaced.equals(concept) ? definition : new AtomicConcept(toBeReplaced.getText());
			return toBeReplaced.equals(concept) ? definition : toBeReplaced;
		} else if (toBeReplaced instanceof AtomicRole) {
			//System.out.println(2);

			//return new AtomicRole(toBeReplaced.getText());
			return  toBeReplaced;

		} else if (toBeReplaced instanceof Exists) {
			//System.out.println(3);
			Formula t1 = AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition);

			return new Exists(toBeReplaced.getSubFormulas().get(0), t1);

		} else if (toBeReplaced instanceof Inclusion) {
			//System.out.println(4);
			Formula t1 = AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition);
			Formula t2 = AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition);
			return new Inclusion(t1, t2);

		} else if(toBeReplaced instanceof Equivalence){
			Formula t1 = AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition);
			Formula t2 = AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition);
			return new Equivalence(t1, t2);
		}

		else if (toBeReplaced instanceof And) {
			//System.out.println(5);

			Set<Formula> conjunct_set = new LinkedHashSet<>();
			for (Formula conjunct : toBeReplaced.getSubformulae()) {
				Formula temp = AckermannReplace(concept, conjunct, definition);
				if(temp instanceof And) {

					//System.out.println(concept+ " "+toBeReplaced+" "+definition);
					conjunct_set.addAll(temp.getSubformulae()); //gaile TODO
					//System.out.println("I find this bug1");

				}
				else conjunct_set.add(temp);
			}
			return  And.getAnd(conjunct_set);
			
		} 
		
		return toBeReplaced;
	}
	
	public static void main(String[] args) {
		/*
		AtomicConcept a = new AtomicConcept("A");
		AtomicConcept b = new AtomicConcept("B");
		AtomicConcept c = new AtomicConcept("C");
		AtomicRole r = new AtomicRole("r");
		Exists e = new Exists(r, b);
		Set<Formula> list = new HashSet<>();
		list.add(a);
		list.add(c);
		And and = new And(list);
		Inclusion inc = new Inclusion(e, and);
		FChecker fc = new FChecker();
		System.out.println("e.c_sig = " + fc.negative(b, inc));
		Inferencer inf = new Inferencer();
		System.out.println("e.c_sig = " + inf.Purify(b, inc));

		 */
		
	}


	public Formula Purify(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? TopConcept.getInstance() : new AtomicConcept(formula.getText());
			
		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Exists) {
			return new Exists(Purify(concept, formula.getSubFormulas().get(0)),
					Purify(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Inclusion) {
			return new Inclusion(Purify(concept, formula.getSubFormulas().get(0)),
					Purify(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof And) {
			Set<Formula> conjunct_list = formula.getSubformulae();
			Set<Formula> conjunct_set = new LinkedHashSet<>();
			for (Formula conjunct : conjunct_list) {
				conjunct_set.add(Purify(concept, conjunct));
			}
			return  And.getAnd(conjunct_set);
			
		}

		return formula;
	}
	
}
