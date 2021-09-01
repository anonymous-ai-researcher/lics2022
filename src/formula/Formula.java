/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package formula;

import concepts.AtomicConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import roles.AtomicRole;

import java.util.ArrayList;
import java.util.*;
import java.util.List;
import java.util.*;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */

public class  Formula {

	private List<Formula> subformulas;
	private Set<Formula> subformulae;
	protected Set<AtomicConcept> c_sig;
	protected Set<AtomicRole> r_sig;
	private String text;

	public Formula() {

	}

	public Formula(String str) {
		this.setText(str);
	}
	
	public Formula(int arity) {
		this.subformulas = new ArrayList<>(arity);

	}
	
	public Set<AtomicConcept> get_c_sig() {
		return c_sig;
	}
	
	public void set_c_sig(AtomicConcept ac) {
		this.c_sig.add(ac);
	}

	public void set_c_sig(Set<AtomicConcept> c_sig) {
		this.c_sig.addAll(c_sig);
	}
	
	public Set<AtomicRole> get_r_sig() {
		return r_sig;
	}
	
	public void set_r_sig(AtomicRole ar) {
		this.r_sig.add(ar);
	}

	public void set_r_sig(Set<AtomicRole> r_sig) {
		this.r_sig.addAll(r_sig);
	}

	public String getText() {
		return this.text;
	}

	public void setText(String text) {
		this.text = text;
	}

	public List<Formula> getSubFormulas() {
		return this.subformulas;
	}
	
	public Set<Formula> getSubformulae() {
		return subformulae;
	}

	public void setSubFormulas(Formula formula) {
		this.subformulas.add(formula);
	}

	public void setSubFormulas(Formula formula1, Formula formula2) {
		this.subformulas.add(formula1);
		this.subformulas.add(formula2);
	}

	public void setSubFormulas(List<Formula> list) {
		this.subformulas.addAll(list);
	}

	public void setSubformulae(Set<Formula> subformulae) {
		this.subformulae = subformulae;
	}

	@Override
	public boolean equals(Object object) {
		if (this == object) {
			return true;
		} else if (object == null || this.getClass() != object.getClass()) {
			return false;
		} else if ((this instanceof AtomicConcept && object instanceof AtomicConcept)
				|| (this instanceof AtomicRole && object instanceof AtomicRole)) {
			return this.toString().equals(object.toString());

		} else if (this instanceof Exists && object instanceof Exists) {
			Exists exi = (Exists) object;
			return this.getSubFormulas().get(0).equals(exi.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(exi.getSubFormulas().get(1));
		} else if (this instanceof Inclusion && object instanceof Inclusion) {
			Inclusion inc = (Inclusion) object;
			return this.getSubFormulas().get(0).equals(inc.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(inc.getSubFormulas().get(1));
		} else if (this instanceof And && object instanceof And) {
			And and = (And) object;
			return this.getSubFormulas().containsAll(and.getSubFormulas())
					&& and.getSubFormulas().containsAll(this.getSubFormulas())
					&& this.getSubFormulas().size() == and.getSubFormulas().size();
		} else {
			return false;
		}

	}

	@Override
	public Formula clone() throws CloneNotSupportedException {

		if (this == TopConcept.getInstance()) {
			return TopConcept.getInstance();

		} else if (this instanceof AtomicConcept) {
			return new AtomicConcept(this.getText());

		} else if (this instanceof AtomicRole) {
			return new AtomicRole(this.getText());

		} else if (this instanceof Exists) {


			return new Exists(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof Inclusion) {

			return new Inclusion(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof And) {

			//List<Formula> conjunct_list = this.getSubFormulas(); ///// bug ?????? TODO
			Set<Formula> conjunct_set = new LinkedHashSet<>();

			for (Formula conjunct : this.getSubformulae()) {
				conjunct_set.add(conjunct.clone());
			}
			return new And(conjunct_set);
			
		}

		return this;
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getSubFormulas()).toHashCode();
	}

}
