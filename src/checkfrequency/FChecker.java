package checkfrequency;

import java.util.HashSet;
import java.util.List;
import java.util.*;

import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;

public class FChecker {

	public FChecker() {

	}
	
	public int positive(AtomicConcept concept, List<Formula> formula_list) {

		int positive = 0;

		for (Formula formula : formula_list) {
			positive = positive + positive(concept, formula);
		}

		return positive;
	}

	public int positive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? 1 : 0;
		} else if (formula instanceof Exists) {
			return positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(concept, formula.getSubFormulas().get(0))
					+ positive(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And) {
			int sum = 0;
			Set<Formula> conjunct_set = formula.getSubformulae();
			for (Formula conjunct : conjunct_set) {
				sum = sum + positive(concept, conjunct);
			}
			return sum;
		}

		return 0;
	}
	
	public static void main(String[] args) {	
		AtomicConcept a = new AtomicConcept("A");
		AtomicConcept b = new AtomicConcept("B");
		AtomicConcept c = new AtomicConcept("C");
		AtomicRole r = new AtomicRole("r");
		Exists e = new Exists(r, b);
		Set<Formula> list1 = new LinkedHashSet<>();
		for (Formula hello : list1) {
			System.out.println("hello = " + hello);
		}
		And and1 = new And(list1);
		Set<Formula> list2 = new LinkedHashSet<>();
		list2.add(a);
		list2.add(b);
		list2.add(e);
		list2.add(e);
		list2.add(b);
		list2.add(c);
		And and2 = new And(list2);
		Inclusion inc = new Inclusion(and2, and1);
		FChecker fc = new FChecker();
		System.out.println("e.c_sig = " + inc);
		System.out.println("e.c_sig = " + fc.negative(b, inc));
		System.out.println("e.c_sig = " + fc.positive(b, inc));
	}

	public int negative(AtomicConcept concept, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(concept, formula);
		}

		return negative;
	}

	public int negative(AtomicConcept concept, Formula formula) {

		if (formula instanceof Exists) {
			return negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(concept, formula.getSubFormulas().get(0))
					+ negative(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And) {
			int sum = 0;
			Set<Formula> conjunct_set = formula.getSubformulae();
			for (Formula conjunct : conjunct_set) {
				sum = sum + negative(concept, conjunct);
			}
			return sum;
		}

		return 0;
	}
	
	public int positive(AtomicRole role, List<Formula> formula_list) {
		
		int positive = 0;
		
		for (Formula formula : formula_list) {
			positive = positive + positive(role, formula);
		}
		
		return positive;		
	}
		
	public int positive(AtomicRole role, Formula formula) {

		if (formula instanceof AtomicRole) {
			return formula.equals(role) ? 1 : 0;
		} else if (formula instanceof Exists) {
			return positive(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return negative(role, formula.getSubFormulas().get(0)) + positive(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And) {
			int sum = 0;
			Set<Formula> conjunct_set = formula.getSubformulae();
			for (Formula conjunct : conjunct_set) {
				sum = sum + positive(role, conjunct);
			}
			return sum;
		}

		return 0;
	}
	
	public int negative(AtomicRole role, List<Formula> formula_list) {

		int negative = 0;

		for (Formula formula : formula_list) {
			negative = negative + negative(role, formula);
		}

		return negative;
	}
	
	public int negative(AtomicRole role, Formula formula) {

		if (formula instanceof Exists) {
			return negative(role, formula.getSubFormulas().get(0)) + negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return positive(role, formula.getSubFormulas().get(0))
					+ negative(role, formula.getSubFormulas().get(1));
		} else if (formula instanceof And) {
			int sum = 0;
			Set<Formula> conjunct_set = formula.getSubformulae(); 
			for (Formula conjunct : conjunct_set) {
				sum = sum + negative(role, conjunct);
			}
			return sum;
		}

		return 0;
	}
	
}
