/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import concepts.ConceptExpression;
import formula.Formula;

/**
 *
 * @author Yizheng
 */
public class Negation extends ConceptExpression {

	public Negation() {
		super();
	}
	
	public Negation(Formula formula) {
		super(formula);
	}

	@Override
	public String toString() {
		Formula formula = this.getSubFormulas().get(0);

		if (formula instanceof And || formula instanceof Or) {
			return "\u00AC(" + formula + ")";
		} else {
			return "\u00AC" + formula;
		}
	}

}
