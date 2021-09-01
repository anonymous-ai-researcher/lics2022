/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import java.util.Set;

import com.google.common.collect.Sets;

import concepts.AtomicConcept;
import formula.Formula;
import roles.AtomicRole;

/**
 *
 * @author Yizheng
 */
public class Equivalence extends Formula {
	
	public Equivalence() {
		super();
	}

	public Equivalence(Formula lefthand, Formula righthand) {
		super(2);
		this.setSubFormulas(lefthand, righthand);
		/*this.c_sig = new HashSet<>();
		this.r_sig = new HashSet<>();
		this.set_c_sig(lefthand.get_c_sig());
		this.set_c_sig(righthand.get_c_sig());
		this.set_r_sig(lefthand.get_r_sig());
		this.set_r_sig(righthand.get_r_sig());*/
	}
	
	public Set<AtomicConcept> get_c_sig() {	
		Formula lefthand = this.getSubFormulas().get(0);
		Formula righthand = this.getSubFormulas().get(1);
		return Sets.union(lefthand.get_c_sig(), righthand.get_c_sig());
	}
	
	public Set<AtomicRole> get_r_sig() {
		Formula lefthand = this.getSubFormulas().get(0);
		Formula righthand = this.getSubFormulas().get(1);
		return Sets.union(lefthand.get_r_sig(), righthand.get_r_sig());
	}

	@Override
	public String toString() {
		Formula lefthand = this.getSubFormulas().get(0);
		Formula righthand = this.getSubFormulas().get(1);

		if ((lefthand instanceof And || lefthand instanceof Or)
				&& (righthand instanceof And || righthand instanceof Or)) {
			return "(" + lefthand + ") \u2261 (" + righthand + ")";
		} else if ((lefthand instanceof And || lefthand instanceof Or) && !(righthand instanceof And)
				&& !(righthand instanceof Or)) {
			return "(" + lefthand + ") \u2261 " + righthand;
		} else if (!(lefthand instanceof And) && !(lefthand instanceof Or)
				&& (righthand instanceof And || righthand instanceof Or)) {
			return lefthand + " \u2261 (" + righthand + ")";
		} else {
			return lefthand + " \u2261 " + righthand;
		}
	}

}
