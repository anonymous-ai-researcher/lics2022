/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import formula.Formula;
import org.apache.commons.lang3.builder.HashCodeBuilder;
import roles.AtomicRole;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.*;

import concepts.AtomicConcept;

/**
 *
 * @author Yizheng
 */
public class And extends Formula {

	public And() {
		super();
	}

	public And(Set<Formula> set) {
		super(set.size());
		this.setSubformulae(set);
		this.setSubFormulas(new ArrayList<>(this.getSubformulae()));
		/*this.c_sig = new HashSet<>();
		this.r_sig = new HashSet<>();
		for (Formula conjunct : set) {
			this.set_c_sig(conjunct.get_c_sig());
			this.set_r_sig(conjunct.get_r_sig());	
		}*/
	}

	public Set<AtomicConcept> get_c_sig() {
		Set<Formula> conjunct_set = this.getSubformulae();
		Set<AtomicConcept> ac_set = new LinkedHashSet<>();
		for (Formula conjunct : conjunct_set) {
			ac_set.addAll(conjunct.get_c_sig());
		}
		return ac_set;
	}
	
	public Set<AtomicRole> get_r_sig() {
		Set<Formula> conjunct_set = this.getSubformulae();
		Set<AtomicRole> ar_set = new LinkedHashSet<>();
		for (Formula conjunct : conjunct_set) {
			ar_set.addAll(conjunct.get_r_sig());
		}
		return ar_set;
	}

	@Override
	public String toString() {
		String str = "";
		int i = 1;
		for (Formula conjunct : this.getSubformulae()) {
			if (i == 1) {
				str = str + conjunct;
			} else {
				str = str + " \u2293 " + conjunct;
			}
			i++;
		}
		return str;
	}

	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getSubformulae()).toHashCode();
	}




	public static  void main(String [] args)throws Exception{
		AtomicConcept a = new AtomicConcept("A");
		AtomicConcept b = new AtomicConcept("B");
		AtomicConcept c = new AtomicConcept("C");
		AtomicConcept d = new AtomicConcept("D");
		AtomicRole r = new AtomicRole("r");
		AtomicRole r2 = new AtomicRole("s");


		Set<Formula> now2 = new LinkedHashSet<>();
		now2.add(c);now2.add(d);
		And and2 = new And(now2);
		Exists ex = new Exists(r2,and2);
		Set<Formula> now = new LinkedHashSet<>();
		now.add(ex);
		now.add(b);
		And and = new And(now);

		Inclusion inc = new Inclusion(new Exists(r,and),c);
		System.out.println(inc.getSubFormulas());
		System.out.println(inc.clone());

	}
	/*public String toString() {
		if (this.getSubFormulas().size() == 1) {
			return this.getSubFormulas().get(0).toString();
		}
		String str = "";
		for (int i = 0; i < this.getSubFormulas().size(); i++) {
			if (i == 0) {
				if (this.getSubFormulas().get(i) instanceof ConceptExpression
						|| this.getSubFormulas().get(i) instanceof RoleExpression
						|| this.getSubFormulas().get(i) instanceof Individual
						|| this.getSubFormulas().get(i) instanceof Negation
						|| this.getSubFormulas().get(i) instanceof Exists
						|| this.getSubFormulas().get(i) instanceof Forall) {
					str = str + this.getSubFormulas().get(i);
					continue;
				}
				str = str + "(" + this.getSubFormulas().get(i) + ")";
				continue;
			}
			if (this.getSubFormulas().get(i) instanceof ConceptExpression
					|| this.getSubFormulas().get(i) instanceof RoleExpression
					|| this.getSubFormulas().get(i) instanceof Individual
					|| this.getSubFormulas().get(i) instanceof Negation
					|| this.getSubFormulas().get(i) instanceof Exists
					|| this.getSubFormulas().get(i) instanceof Forall) {
				str = str + " \u2293 " + this.getSubFormulas().get(i);
				continue;
			}
			str = str + " \u2293 " + "(" + this.getSubFormulas().get(i) + ")";
		}
		return str + "";
	}*/
}
