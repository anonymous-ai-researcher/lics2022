/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package roles;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */
public class  TopRole extends RoleExpression {

	private static final TopRole TR = new TopRole();

	public TopRole() {
		super("\u25BD");
	}

	public static TopRole getInstance() {
		return TR;
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
