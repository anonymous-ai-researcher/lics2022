/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package checkexistence;

import java.util.Set;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Inclusion;
import formula.Formula;
import roles.AtomicRole;

/**
 *
 * @author Yizheng311
 */
public class EChecker {

	public EChecker() {

	}

	public boolean isPresent(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept);
		} else if (formula instanceof Exists) {
			return isPresent(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof Inclusion) {
			return isPresent(concept, formula.getSubFormulas().get(0))
					|| isPresent(concept, formula.getSubFormulas().get(1));
		} else if (formula instanceof And) {
			Set<Formula> operand_set = formula.getSubformulae();
			for (Formula operand : operand_set) {
				if (isPresent(concept, operand)) {
					return true;
				}
			}
		}
		return false;
	}

	public boolean isPresent(AtomicRole role, Formula formula) {

		if (formula instanceof AtomicRole) {
			return formula.equals(role);
		} else if (formula instanceof Exists || formula instanceof Inclusion) {
			return isPresent(role, formula.getSubFormulas().get(0))////////
					|| isPresent(role, formula.getSubFormulas().get(1));///////
		} else if (formula instanceof And) {
			Set<Formula> operand_set = formula.getSubformulae();
			for (Formula operand : operand_set) {
				if (isPresent(role, operand)) {
					return true;
				}
			}
		}

		return false;
	}

}
