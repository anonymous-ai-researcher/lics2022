/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package concepts;

import java.util.*;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */
public class TopConcept extends ConceptExpression {

	private static final TopConcept TC = new TopConcept();

	public TopConcept() {
		super("\u22A4");
		this.c_sig = new LinkedHashSet<>();
		this.r_sig = new LinkedHashSet<>();
	}

	public static TopConcept getInstance() {
		return TC;
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
