/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import concepts.ConceptExpression;
import roles.RoleExpression;
import individual.Individual;
import formula.Formula;

import java.util.List;

/**
 *
 * @author Yizheng
 */
public class Or extends Formula {

	public Or() {
		super();
	}
	
	public Or(List<Formula> list) {
		super(list.size());
		this.setSubFormulas(list);
	}

	@Override
	public String toString() {
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
				str = str + " \u2294 " + this.getSubFormulas().get(i);
				continue;
			}
			str = str + " \u2294 " + "(" + this.getSubFormulas().get(i) + ")";
		}
		return str + "";
	}
}
