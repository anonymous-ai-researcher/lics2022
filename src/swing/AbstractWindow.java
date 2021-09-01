package swing;

import javax.swing.JFrame;

public abstract class AbstractWindow extends JFrame {

	private static final long serialVersionUID = 1L;

	protected abstract void addListener();

	protected abstract void registerComponent();

	protected abstract void init();

	protected void initWindow() {
		setSize(800, 600);
		setLocationRelativeTo(null);
		setVisible(true);
		setResizable(false);
		setDefaultCloseOperation(JFrame.DISPOSE_ON_CLOSE);
	}

	public final void run() {
		initWindow();
		init();
		registerComponent();
		addListener();
	}
}
