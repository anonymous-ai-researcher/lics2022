package swing;

import java.util.ArrayList;
import java.util.List;

import javax.swing.AbstractListModel;

public class SentenceListModel<T> extends AbstractListModel<T> {

	private static final long serialVersionUID = 1L;

	private List<T> list;

	public SentenceListModel() {
		this(new ArrayList<T>());
	}

	public SentenceListModel(List<T> newsList) {
		list = newsList;
	}

	public void notifyDataChanged() {
		fireContentsChanged(this, 0, getSize());
	}

	public T getElementAt(int arg0) {
		return list.get(arg0);
	}

	public int getSize() {
		return list.size();
	}

	public void setListData(List<T> newsList) {
		list = newsList;
		notifyDataChanged();
	}

	public List<T> getListData() {
		return list;
	}
	
	public void removeAllElements() {
		list.removeAll(list);
	}
}
