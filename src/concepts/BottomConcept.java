/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */
public class BottomConcept extends ConceptExpression {

	private static final BottomConcept BC = new BottomConcept();

	public BottomConcept() {
		super("\u22A5");
	}

	public static BottomConcept getInstance() {
		return BC;
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getClass()).toHashCode();
	}
}
