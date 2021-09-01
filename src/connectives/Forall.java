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
public class Forall extends ConceptExpression {

	public Forall() {
		super();
	}

	public Forall(Formula role, Formula filler) {
		super(role, filler);
	}

	@Override
	public String toString() {
		Formula role = this.getSubFormulas().get(0);
		Formula filler = this.getSubFormulas().get(1);

		if (filler instanceof And || filler instanceof Or) {
			return "\u2200" + role + ".(" + filler + ")";
		} else {
			return "\u2200" + role + "." + filler;
		}
	}
}
