package extraction;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import com.google.common.collect.Sets;

import concepts.AtomicConcept;
import formula.Formula;
import roles.AtomicRole;

public class SubsetExtractor {
	int i  =0;
	public SubsetExtractor() {
		i = 1;
	}
	
	public List<Formula> getConceptSubset(AtomicConcept concept, List<Formula> formula_list) {
		
		List<Formula> output_list = new ArrayList<>();
		int len = formula_list.size();
		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicConcept> c_set = formula.get_c_sig();
			if (c_set.contains(concept)) {
				//System.out.println("pivot concept = " + formula);
				//System.out.println("Formula 1 [" + i + "] = " + formula);
				output_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return output_list;
	}
		
	public List<Formula> getConceptSubset(Set<AtomicConcept> c_sig, List<Formula> formula_list) {

		List<Formula> c_sig_list = new ArrayList<>();
		int len = formula_list.size();
		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicConcept> c_set = formula.get_c_sig();
			if (!Sets.intersection(c_set, c_sig).isEmpty()) {
				c_sig_list.add(formula);
				formula_list.remove(i);
				i--;
			}
			//System.out.println("Formula 2 [" + i +"] = " + formula);
		}
		return c_sig_list;
	}
		
	public List<Formula> getRoleSubset(AtomicRole role, List<Formula> formula_list) {

		List<Formula> role_list = new ArrayList<>();
		int len = formula_list.size();
		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicRole> r_set = formula.get_r_sig();
			if (r_set.contains(role)) {
				//System.out.println("pivot role = " + role);
				//System.out.println("Formula 3 [" + i +"] = " + formula);
				role_list.add(formula);
				formula_list.remove(i);
				i--;
			}
		}

		return role_list;
	}
	
	public List<Formula> getRoleSubset(Set<AtomicRole> r_sig, List<Formula> formula_list) {

		List<Formula> r_sig_list = new ArrayList<>();
		int len = formula_list.size();
		for (int i = 0; i < formula_list.size(); i++) {
			Formula formula = formula_list.get(i);
			Set<AtomicRole> r_set = formula.get_r_sig();
			if (!Sets.intersection(r_set, r_sig).isEmpty()) {
				r_sig_list.add(formula);
				formula_list.remove(i);
				i--;
			}
			//System.out.println("Formula 4 [" + i +"] = " + formula);
		}

		return r_sig_list;
	}
	public static void main(String [] args){
		SubsetExtractor sb = new SubsetExtractor();
	}

}
