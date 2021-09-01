package simplification;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


import com.google.common.collect.Lists;

import checkexistence.EChecker;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.BottomRole;
import roles.TopRole;

public class Simplifier {

	public Simplifier() {

	}
				
	/*public List<Formula> getSimplifiedForm(List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula unsimplified : input_list) {

			Formula simplified = getSimplifiedForm(unsimplified);

			if (simplified == TopConcept.getInstance()) {
				
			} else if (simplified instanceof And) {
				output_list.addAll(simplified.getSubFormulas());
				
			} else {
				output_list.add(simplified);
			}
			
		}

		return output_list;
	}
	//
	public Formula getSimplifiedForm(Formula formula) throws CloneNotSupportedException {
		
		//formula = toEL(formula);
	
		while (!(formula.equals(simplifiedForm(formula)))) {
			formula = simplifiedForm(formula);
		}
		
		//formula = toALC(formula);
		
		return formula;
	}
	
	
	public Formula simplifiedForm(final Formula input) throws CloneNotSupportedException {

		Formula formula = input.clone();

		formula = simplified_1(formula);

		return formula;
	}

	private Formula simplified_1(Formula formula) {

		if (formula instanceof Inclusion) {

			formula.getSubFormulas().set(0, simplified_1(formula.getSubFormulas().get(1)));
			formula.getSubFormulas().set(1, simplified_1(formula.getSubFormulas().get(1)));

		} else if (formula instanceof Exists) {

			formula.getSubFormulas().set(1, simplified_1(formula.getSubFormulas().get(1)));

		} else if (formula instanceof And) {

			EChecker ec = new EChecker();
			
			List<Formula> operand_list = formula.getSubFormulas();
			List<Formula> new_operand_list = new ArrayList<>();
			for (Formula operand : operand_list) {
				Formula new_operand = simplified_2(operand);
				if (!new_operand_list.contains(new_operand)) {
					new_operand_list.add(new_operand);
				}
			}
			if (new_operand_list.size() == 1) {
				return simplified_2(new_operand_list.get(0));
			} else {
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_operand_list);
			}	

			if (formula.getSubFormulas().size() == 1) {
				return simplified_1(formula.getSubFormulas().get(0));

			} else if (ec.isAndInAnd(formula)) {
				List<Formula> conjunct_list = formula.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();

				for (Formula conjunct : conjunct_list) {
					if (conjunct instanceof And) {
						new_conjunct_list.addAll(conjunct.getSubFormulas());
					} else {
						new_conjunct_list.add(conjunct);
					}
				}
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_conjunct_list);
				return simplified_1(formula);

			} else {
				for (int i = 0; i < formula.getSubFormulas().size(); i++) {
					formula.getSubFormulas().set(i, simplified_1(formula.getSubFormulas().get(i)));
				}
			}
		}

		return formula;
	}*/
	
	/*private Formula simplified_2(Formula formula) {

		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, simplified_2(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists) {
			formula.getSubFormulas().set(1, simplified_2(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			List<Formula> new_operand_list = new ArrayList<>();
			for (Formula operand : operand_list) {
				Formula new_operand = simplified_2(operand);
				if (!new_operand_list.contains(new_operand)) {
					new_operand_list.add(new_operand);
				}
			}
			if (new_operand_list.size() == 1) {
				return new_operand_list.get(0);
			} else {
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_operand_list);
				return formula;
			}		
		}

		return formula;
	}*/
	
	// And(A,B,A)=And(A,B)
	/*private Formula simplified_2(Formula formula) {

		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, simplified_2(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(1, simplified_2(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			List<Formula> operand_list = formula.getSubFormulas();
			List<Formula> new_operand_list = new ArrayList<>();
			for (Formula operand : operand_list) {
				Formula new_operand = simplified_2(operand);
				if (!new_operand_list.contains(new_operand)) {
					new_operand_list.add(new_operand);
				}
			}
			if (new_operand_list.size() == 1) {
				return new_operand_list.get(0);
			} else {
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_operand_list);
				return formula;
			}		
		}

		return formula;
	}
	
	/*private Formula simplified_3(Formula formula) {

		if (formula instanceof Negation) {
			formula.getSubFormulas().set(0, simplified_3(formula.getSubFormulas().get(0)));
			return formula;

		} else if (formula instanceof Exists) {
			formula.getSubFormulas().set(1, simplified_3(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			
			for (int i = 0; i < disjunct_list.size(); i++) {					
				if (disjunct_list.get(i) instanceof Negation) {
				    if (disjunct_list.get(i).getSubFormulas().get(0) == BottomConcept.getInstance()) {
				    	return disjunct_list.get(i);
				    	
				    } else if (disjunct_list.get(i).getSubFormulas().get(0) instanceof AtomicConcept
				    		|| disjunct_list.get(i).getSubFormulas().get(0) instanceof Exists) {
				    	for (int j = 0; j < disjunct_list.size(); j++) {
				    		if (j != i && disjunct_list.get(j).equals(disjunct_list.get(i).getSubFormulas().get(0))) {
				    			return new Negation(BottomConcept.getInstance());
				    		}
				    	}    	
			
				    } else if (disjunct_list.get(i).getSubFormulas().get(0) instanceof Or) {
				    	List<Formula> inner_disjunct_list = disjunct_list.get(i).getSubFormulas().get(0).getSubFormulas();
				    	if (disjunct_list.containsAll(inner_disjunct_list)) {
				    		return new Negation(BottomConcept.getInstance());
				    	}
				    	
				    }		    
				}
				
				if (disjunct_list.get(i) != BottomConcept.getInstance()) {
					new_disjunct_list.add(simplified_3(disjunct_list.get(i)));
				}
			}

			if (new_disjunct_list.isEmpty()) {
				return BottomConcept.getInstance();
				
			} else if (new_disjunct_list.size() == 1) {
				return new_disjunct_list.get(0);
				
			} else {
				formula.getSubFormulas().clear();
				formula.getSubFormulas().addAll(new_disjunct_list);
				return formula;				
			}
		}

		return formula;
	}*/

	// And(A,B,~A)=false, Or(A,B,~A)=true
	
	/*public List<Formula> getNNF(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.add(getNNF(formula));
		}

		return output_list;
	}

	
	public Formula getNNF(Formula formula) {

		if (formula instanceof Negation) {
			Formula operand = formula.getSubFormulas().get(0);

			if (operand == TopConcept.getInstance()) {
				return BottomConcept.getInstance();
				
			} else if (operand == BottomConcept.getInstance()) {
				return TopConcept.getInstance();
				
			} else if (operand instanceof Negation) {
				return getNNF(operand.getSubFormulas().get(0));
				
			} else if (operand instanceof Exists) {
				return new Forall(getNNF(operand.getSubFormulas().get(0)),
						getNNF(new Negation(operand.getSubFormulas().get(1))));
				
			} else if (operand instanceof Forall) {
				return new Exists(getNNF(operand.getSubFormulas().get(0)),
						getNNF(new Negation(operand.getSubFormulas().get(1))));
				
			} else if (operand instanceof And) {
				List<Formula> conjunct_list = operand.getSubFormulas();
				List<Formula> new_conjunct_list = new ArrayList<>();
				for (Formula conjunct : conjunct_list) {
					new_conjunct_list.add(getNNF(new Negation(conjunct)));
				}
				return new Or(new_conjunct_list);
				
			} else if (operand instanceof Or) {
				List<Formula> disjunct_list = operand.getSubFormulas();
				List<Formula> new_disjunct_list = new ArrayList<>();
				for (Formula disjunct : disjunct_list) {
					new_disjunct_list.add(getNNF(new Negation(disjunct)));
				}
				return new And(new_disjunct_list);
				
			} else {
				return formula;
			}

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(0, getNNF(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, getNNF(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, getNNF(formula.getSubFormulas().get(i)));
			}
			return formula;
		}

		return formula;
	}
	
	public List<Formula> getCNF(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(getCNF(formula));
		}
		return output_list;
	}
	
	static int i = 0; */

	/*public List<Formula> getCNF(Formula formula) {

		EChecker ec = new EChecker();
		
		if (ec.isAndInOr(formula)) {
			i++;
			//System.out.println("i = " + i);
			List<List<Formula>> list_list = new ArrayList<>();
			List<Formula> disjunct_list = formula.getSubFormulas();
			for (int i = 0; i < disjunct_list.size(); i++) {
				list_list.add(i, new ArrayList<>());
				if (disjunct_list.get(i) instanceof And) {
					list_list.get(i).addAll(disjunct_list.get(i).getSubFormulas());
				} else {
					list_list.get(i).add(disjunct_list.get(i));
				}
			}

			List<Formula> output_list = new ArrayList<>();
			List<List<Formula>> cp_list = Lists.cartesianProduct(list_list);
			
			for (List<Formula> list : cp_list) {
				output_list.add(new Or(list));
			}

			return output_list;		
		}		
		
		return Collections.singletonList(formula);
	}
	
	public Formula getDNF(Formula formula) {

		EChecker ec = new EChecker();

		if (ec.isOrInAnd(formula)) {

			List<List<Formula>> list_list = new ArrayList<>();
			List<Formula> conjunct_list = formula.getSubFormulas();

			for (int i = 0; i < conjunct_list.size(); i++) {
				list_list.add(i, new ArrayList<>());
				if (conjunct_list.get(i) instanceof Or) {
					list_list.get(i).addAll(conjunct_list.get(i).getSubFormulas());
				} else {
					list_list.get(i).add(conjunct_list.get(i));
				}
			}

			List<Formula> output_list = new ArrayList<>();
			List<List<Formula>> cp_list = Lists.cartesianProduct(list_list);
			
			for (List<Formula> list : cp_list) {
				output_list.add(new And(list));
			}

			Formula output = new Or(output_list);
			return output;
		}

		return formula;
	}
	
	public Formula removeDoubleNegations(Formula formula) {

		if (formula instanceof Negation) {
			Formula operand = formula.getSubFormulas().get(0);

			if (operand == TopConcept.getInstance()) {
				return BottomConcept.getInstance();
				
			} else if (operand == BottomConcept.getInstance()) {
				return TopConcept.getInstance();
				
			} else if (operand == TopRole.getInstance()) {
				return BottomRole.getInstance();
				
			} else if (operand == BottomRole.getInstance()) {
				return TopRole.getInstance();
				
			} else if (operand instanceof Negation) {
				return removeDoubleNegations(operand.getSubFormulas().get(0));

			} else {
				formula.getSubFormulas().set(0, removeDoubleNegations(operand));
				return formula;
			}

		} else if (formula instanceof Exists || formula instanceof Forall) {
			formula.getSubFormulas().set(0, removeDoubleNegations(formula.getSubFormulas().get(0)));
			formula.getSubFormulas().set(1, removeDoubleNegations(formula.getSubFormulas().get(1)));
			return formula;

		} else if (formula instanceof And || formula instanceof Or) {
			for (int i = 0; i < formula.getSubFormulas().size(); i++) {
				formula.getSubFormulas().set(i, removeDoubleNegations(formula.getSubFormulas().get(i)));
			}
			return formula;
		}

		return formula;
	}
		

	public List<Formula> getClauses(List<Formula> input_list) {

		List<Formula> output_list = new ArrayList<>();

		for (Formula axiom : input_list) {
			output_list.add(getClause(axiom));
		}
		return output_list;
	}

	private Formula getClause(Formula formula) {
		
		if (formula instanceof Inclusion) {
			List<Formula> disjunct_list = new ArrayList<>();

			Formula subsumee = formula.getSubFormulas().get(0);
			Formula subsumer = formula.getSubFormulas().get(1);
			
			if (subsumee instanceof Negation) {
				disjunct_list.add(subsumee.getSubFormulas().get(0));
			} else {
				disjunct_list.add(new Negation(subsumee));	
			}
			
			disjunct_list.add(subsumer);
			
			Formula clause = new Or(disjunct_list);
			return clause;
			
		}
		
		return null;
	}*/

}
