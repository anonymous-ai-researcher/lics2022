package swing;

import java.util.HashMap;

public class Register {
	private static Register instance = null;
	private HashMap<String, Object> map;

	private Register() {
		map = new HashMap<String, Object>();
	}

	public static Register getInstance() {
		if (instance == null)
			instance = new Register();
		return instance;
	}

	public void registerObject(String str, Object obj) {
		map.put(str, obj);
	}

	public Object getObject(String str) {
		return map.get(str);
	}
}