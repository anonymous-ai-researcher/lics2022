package inference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.*;

import BackTrack.BackTrack;
import checkTautology.TautologyChecker;
import checkexistence.EChecker;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.apibinding.OWLManager;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import roles.AtomicRole;
import org.semanticweb.owlapi.apibinding.OWLManager;

public class DefinerIntroducer {

	public DefinerIntroducer() {
		definer_left_map = new HashMap<>();
		definer_left_map = new HashMap<>();
		owldefiner_set = new LinkedHashSet<>();
		definer_set = new LinkedHashSet<>();
	}

	public  Map<Formula, AtomicConcept> definer_left_map = new HashMap<>();
	public  Map<Formula, AtomicConcept> definer_right_map = new HashMap<>();
	public  Map<AtomicConcept, Formula> reverse_definer_left_map = new HashMap<>();
	public  Map<AtomicConcept, Formula> reverse_definer_right_map = new HashMap<>();
	public  Set<OWLEntity> owldefiner_set = new LinkedHashSet<>();
	public  Set<AtomicConcept> definer_set = new LinkedHashSet<>();

	public List<Formula> removeCyclicDefinition(AtomicConcept concept,List<Formula> beforeIntroDefiners){
		FChecker fc = new FChecker();
		List<Formula> ans = new ArrayList<>();
		for(Formula formula : beforeIntroDefiners){
			if(fc.negative(concept,formula) > 0 && fc.positive(concept,formula) > 0){

			}
			else{
				ans.add(formula);
			}
		}
		return ans;
	}
	public List<Formula> introduceDefiners(AtomicConcept concept, List<Formula> input_list)
			throws Exception {

		Set<Formula> output_list = new LinkedHashSet<>();
		/*
		System.out.println("input list");
		for(Formula formula : input_list){
			System.out.println(formula);
		}

		 */
		for (Formula formula : input_list) {
			//Formula formulaClone = formula.clone();
			//Formula outputFormula = formula.clone();
			List<Formula> re = introduceDefiners(concept, formula);

			output_list.addAll(re);
			if(re.size() <= 1) continue;

			System.out.println("original formla : " );
			System.out.println(formula+" "+concept);
			System.out.println("after introduced :");
			for(Formula temp : re){
				System.out.println(temp);

			}
			System.out.println("--------------------" );





		}


		return new ArrayList<>(output_list);
	}


	public List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) throws Exception{

		List<Formula> output_list = new ArrayList<>();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();

		Formula subsumee = formula.getSubFormulas().get(0);
		Formula subsumer = formula.getSubFormulas().get(1);
		int A_subsumee = fc.positive(concept, subsumee);
		int A_subsumer = fc.positive(concept, subsumer);

		if (subsumee.equals(subsumer)) {

		} else if (subsumee instanceof And && subsumee.getSubformulae().contains(subsumer)) {


		} else if (A_subsumee == 0 && A_subsumer == 0) {
			output_list.add(formula);

		} else if (A_subsumee == 1 && A_subsumer == 0) {

			if (subsumee instanceof Exists) {
				Formula filler = subsumee.getSubFormulas().get(1);
				if (filler instanceof Exists ||
						(filler instanceof And && !filler.getSubformulae().contains(concept))) {
					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(concept, conjunct) && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);
						// B and exists r.exists s.A in C
						if (filler instanceof Exists ||
								(filler instanceof And && !filler.getSubformulae().contains(concept))) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
							// B and exists r.(C and exists s.A)
						} else {
							output_list.add(formula);
							break;
						}

					} else if (conjunct.equals(concept)) {
						output_list.add(formula);
						break;
					}
				}

			} else {
				output_list.add(formula);
			}

		} else if (A_subsumee > 1 && A_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (conjunct instanceof Exists && ec.isPresent(concept, conjunct) ) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());

							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							reverse_definer_right_map.put(definer,filler);

							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							break;
						}
					}
				}
			}

		} else if (A_subsumee == 0 && A_subsumer == 1) {

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						reverse_definer_left_map.put(definer,filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, filler)));

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And && !filler.getSubformulae().contains(concept)) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						reverse_definer_left_map.put(definer,filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						Set<Formula> conjunct_set = filler.getSubformulae();
						for (Formula conjunct : conjunct_set) {

							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, conjunct)));
						}

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else {
				output_list.add(formula);
			}

		} else if (A_subsumee == 1 && A_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (filler instanceof Exists ||
						filler instanceof And && !filler.getSubformulae().contains(concept)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);

						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						reverse_definer_left_map.put(definer,subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
                        output_list.add(formula);
					}

				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(concept, conjunct) && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (filler instanceof Exists ||
								filler instanceof And && !filler.getSubformulae().contains(concept)) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else {

							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								reverse_definer_left_map.put(definer,subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}

						}

					} else if (conjunct.equals(concept)) {

						if (definer_left_map.get(subsumer) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_left_map.put(subsumer, definer);
							reverse_definer_left_map.put(definer,subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
							break;

						} else {
							AtomicConcept definer = definer_left_map.get(subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							break;
						}
					}
				}

			} else {

				if (definer_left_map.get(subsumer) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(subsumer, definer);
					reverse_definer_left_map.put(definer,subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

				} else {
					AtomicConcept definer = definer_left_map.get(subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			}
////////////////////////////////
		} else if (A_subsumee > 1 && A_subsumer == 1) {
			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
					output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();
				int tag = 0;
				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(concept, conjunct) ) {
						if(conjunct instanceof Exists) {//gaile
							tag = 1;
							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								//System.out.println(formula+" // "+concept);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}
						}


					}
				}
				if(tag == 0){

				//	throw new Exception();
				}
			}

		} else if (A_subsumee == 0 && A_subsumer > 1) {

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (filler instanceof Exists) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						reverse_definer_left_map.put(definer,filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, filler)));

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else if (filler instanceof And) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						reverse_definer_left_map.put(definer,filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						Set<Formula> conjunct_set = filler.getSubformulae();
						for (Formula conjunct : conjunct_set) {
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, conjunct)));
						}

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);

					}
				}
			}

		} else if (A_subsumee == 1 && A_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (filler instanceof Exists ||
						filler instanceof And && !filler.getSubformulae().contains(concept)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);

						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
						output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(concept, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						reverse_definer_left_map.put(definer,subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(concept, conjunct) && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (filler instanceof Exists ||
								filler instanceof And && !filler.getSubformulae().contains(concept)) {

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else {

							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								reverse_definer_left_map.put(definer,subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}

					} else if (conjunct.equals(concept)) {

						if (definer_left_map.get(subsumer) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_left_map.put(subsumer, definer);
							reverse_definer_left_map.put(definer,subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));
							break;

						} else {
							AtomicConcept definer = definer_left_map.get(subsumer);
							formula.getSubFormulas().set(1, definer);
							output_list.add(formula);
							break;
						}
					}
				}

			} else {

				if (definer_left_map.get(subsumer) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(subsumer, definer);
					reverse_definer_left_map.put(definer,subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(concept, new Inclusion(definer, subsumer)));

				} else {
					AtomicConcept definer = definer_left_map.get(subsumer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			}

		} else if (A_subsumee > 1 && A_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
					output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(concept, formula));
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(concept, conjunct) && conjunct instanceof Exists) {

						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							reverse_definer_right_map.put(definer,filler);

							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							output_list.addAll(introduceDefiners(concept, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(concept, formula));
							break;
						}
					}
				}
			}

		} else {
			output_list.add(formula);
		}

		return output_list;
	}

















	public List<Formula> introduceDefiners(AtomicRole role, List<Formula> input_list)
			throws Exception {

		List<Formula> output_list = new ArrayList<>();


		for (Formula formula : input_list) {
			//System.out.println(formula);
			List<Formula> re = introduceDefiners(role, formula);

			output_list.addAll(re);

			 if(re.size() <= 1) continue;


			/*
			System.out.println("original formla and role: " );
			System.out.println(formula+" "+role);
			System.out.println("after introduced :");
			for(Formula temp : re){
				System.out.println(temp);

			}
			System.out.println("--------------------" );

			 */



		}
		return output_list;


	}

	public List<Formula> introduceDefiners(AtomicRole role, Formula formula)throws Exception {
		//Formula formula = formula1.clone();
		List<Formula> output_list = new ArrayList<>();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();

		Formula subsumee = formula.getSubFormulas().get(0);
		Formula subsumer = formula.getSubFormulas().get(1);

		int r_subsumee = fc.positive(role, subsumee);
		int r_subsumer = fc.positive(role, subsumer);


		if (subsumee.equals(subsumer)) {

		} else if (subsumee instanceof And && subsumee.getSubformulae().contains(subsumer)) {


		} else if (r_subsumee == 0 && r_subsumer == 0) {
			output_list.add(formula);

		} else if (r_subsumee == 1 && r_subsumer == 0) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);

						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(role, conjunct)) {
						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}

						} else {
							output_list.add(formula);
							break;
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee > 1 && r_subsumer == 0) {
			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			} else if (subsumee instanceof And) {

				for (Formula conjunct : subsumee.getSubformulae()) {
/*
					if (ec.isPresent(role, conjunct)) {
						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							System.out.println(role+" "+formula);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}
					}
					*/

					if (ec.isPresent(role, conjunct)) {

                        if (definer_right_map.get(conjunct) == null) {
                            AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
                            AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
                            definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
                            definer_right_map.put(conjunct, definer);
							reverse_definer_right_map.put(definer,conjunct);
                            subsumee.getSubformulae().remove(conjunct);
                            subsumee.getSubformulae().add(definer);
                            //conjunct.getSubFormulas().set(1, definer);

                            output_list.addAll(introduceDefiners(role, formula));
                            output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
                            break;

                        } else {
                            AtomicConcept definer = definer_right_map.get(conjunct);
                            //conjunct.getSubFormulas().set(1, definer);
							subsumee.getSubformulae().remove(conjunct);
							subsumee.getSubformulae().add(definer);
                            output_list.addAll(introduceDefiners(role, formula));
                            break;
                        }
                    }
				}
			}

		} else if (r_subsumee == 0 && r_subsumer == 1) {

			if (subsumer instanceof Exists) {

				Formula relation = subsumer.getSubFormulas().get(0);
				Formula filler = subsumer.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_left_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(filler, definer);
						reverse_definer_left_map.put(definer,filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
						if (filler instanceof And) {
							Set<Formula> filler_conjunct_set = filler.getSubformulae();
							for (Formula conjunct : filler_conjunct_set) {
								output_list.addAll(introduceDefiners(role, new Inclusion(definer, conjunct)));
							}

						} else {
							output_list.addAll(introduceDefiners(role, new Inclusion(definer, filler)));
						}

					} else {
						AtomicConcept definer = definer_left_map.get(filler);
						subsumer.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}

				} else {
					output_list.add(formula);
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee == 1 && r_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);

						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						reverse_definer_left_map.put(definer,subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));


					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(role, conjunct)) {

						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Inclusion(filler,definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {

							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								reverse_definer_left_map.put(definer,subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else if (r_subsumee > 1 && r_subsumer == 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(role, conjunct)) {
/*
						Formula filler = conjunct.getSubFormulas().get(1);

						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}

 */

                    if (definer_right_map.get(conjunct) == null) {
                        AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
                        AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
                        definer_set.add(definer);
                        // owldefiner_set.add(bc.getClassfromConcept(definer));
                        definer_right_map.put(conjunct, definer);
						reverse_definer_right_map.put(definer,conjunct);

						//Formula conjunct_temp = conjunct.clone();
                        subsumee.getSubformulae().remove(conjunct);
                        subsumee.getSubformulae().add(definer);
                        //conjunct.getSubFormulas().set(1, definer);

                        output_list.addAll(introduceDefiners(role, formula));
                        output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
                        break;

                    } else {
                        AtomicConcept definer = definer_right_map.get(conjunct);
                        //conjunct.getSubFormulas().set(1, definer);
						subsumee.getSubformulae().remove(conjunct);
						subsumee.getSubformulae().add(definer);
                        output_list.addAll(introduceDefiners(role, formula));
                        break;
                    }
					}
				}
			}

		} else if (r_subsumee == 0 && r_subsumer > 1) {

			if (subsumer instanceof Exists) {

				Formula filler = subsumer.getSubFormulas().get(1);

				if (definer_left_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_left_map.put(filler, definer);
					reverse_definer_left_map.put(definer,filler);
					subsumer.getSubFormulas().set(1, definer);
					output_list.add(formula);
					if (filler instanceof And) {
						Set<Formula> filler_conjunct_set = filler.getSubformulae();
						for (Formula conjunct : filler_conjunct_set) {
							output_list.addAll(introduceDefiners(role, new Inclusion(definer, conjunct)));
						}

					} else {
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, filler)));
					}

				} else {
					AtomicConcept definer = definer_left_map.get(filler);
					subsumer.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}
			}

		} else if (r_subsumee == 1 && r_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula relation = subsumee.getSubFormulas().get(0);
				Formula filler = subsumee.getSubFormulas().get(1);

				if (!relation.equals(role)) {

					if (definer_right_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_right_map.put(filler, definer);
						reverse_definer_right_map.put(definer,filler);

						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
						output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

					} else {
						AtomicConcept definer = definer_right_map.get(filler);
						subsumee.getSubFormulas().set(1, definer);
						output_list.addAll(introduceDefiners(role, formula));
					}

				} else {

					if (definer_left_map.get(subsumer) == null) {
						AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						// owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_left_map.put(subsumer, definer);
						reverse_definer_left_map.put(definer,subsumer);

						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));

					} else {
						AtomicConcept definer = definer_left_map.get(subsumer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(role, conjunct)) {

						Formula relation = conjunct.getSubFormulas().get(0);

						if (!relation.equals(role)) {

							Formula filler = conjunct.getSubFormulas().get(1);

							if (definer_right_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_right_map.put(filler, definer);
								reverse_definer_right_map.put(definer,filler);

								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
								break;

							} else {
								AtomicConcept definer = definer_right_map.get(filler);
								conjunct.getSubFormulas().set(1, definer);
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {

							if (definer_left_map.get(subsumer) == null) {
								AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								// owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_left_map.put(subsumer, definer);
								reverse_definer_left_map.put(definer,subsumer);

								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								output_list.addAll(introduceDefiners(role, new Inclusion(definer, subsumer)));
								break;

							} else {
								AtomicConcept definer = definer_left_map.get(subsumer);
								formula.getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}
					}
				}
			}

		} else if (r_subsumee > 1 && r_subsumer > 1) {

			if (subsumee instanceof Exists) {

				Formula filler = subsumee.getSubFormulas().get(1);

				if (definer_right_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					// owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_right_map.put(filler, definer);
					reverse_definer_right_map.put(definer,filler);

					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
					output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));

				} else {
					AtomicConcept definer = definer_right_map.get(filler);
					subsumee.getSubFormulas().set(1, definer);
					output_list.addAll(introduceDefiners(role, formula));
				}

			} else if (subsumee instanceof And) {

				Set<Formula> conjunct_set = subsumee.getSubformulae();

				for (Formula conjunct : conjunct_set) {

					if (ec.isPresent(role, conjunct)) {
/*
						Formula filler = conjunct.getSubFormulas().get(1);


						if (definer_right_map.get(filler) == null) {
							AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
							AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
							definer_set.add(definer);
							// owldefiner_set.add(bc.getClassfromConcept(definer));
							definer_right_map.put(filler, definer);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							output_list.addAll(introduceDefiners(role, new Inclusion(filler, definer)));
							break;

						} else {
							AtomicConcept definer = definer_right_map.get(filler);
							conjunct.getSubFormulas().set(1, definer);
							output_list.addAll(introduceDefiners(role, formula));
							break;
						}

 */
                        if (definer_right_map.get(conjunct) == null) {
                            AtomicConcept definer = new AtomicConcept("Definer" + AtomicConcept.getDefiner_index());
                            AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
                            definer_set.add(definer);
                            // owldefiner_set.add(bc.getClassfromConcept(definer));
                            definer_right_map.put(conjunct, definer);
							reverse_definer_right_map.put(definer,conjunct);

							//Formula conjunct_temp = conjunct.clone();
                            subsumee.getSubformulae().remove(conjunct);
                            subsumee.getSubformulae().add(definer);
                            //conjunct.getSubFormulas().set(1, definer);
                            output_list.addAll(introduceDefiners(role, formula));
                            output_list.addAll(introduceDefiners(role, new Inclusion(conjunct, definer)));
                            break;

                        } else {
                            AtomicConcept definer = definer_right_map.get(conjunct);
                            //conjunct.getSubFormulas().set(1, definer);
							subsumee.getSubformulae().remove(conjunct);
							subsumee.getSubformulae().add(definer);
                            output_list.addAll(introduceDefiners(role, formula));
                            break;
                        }
					}
				}
			}

		} else {
			output_list.add(formula);
		}

		return output_list;
	}


}
