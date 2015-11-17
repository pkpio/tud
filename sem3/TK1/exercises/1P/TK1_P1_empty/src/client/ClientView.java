package client;

import java.rmi.RemoteException;

/**
 * The client GUI logic appears here
 * 
 * 
 * @author praveen
 */
public class ClientView {
	ClientApp mApp;
	ClientCtrl mController;

	/**
	 * Creates an instance of the Client view.
	 * 
	 * @param app
	 *            A reference to the application object
	 * @param controller
	 *            A reference to the client controller
	 */
	public ClientView(ClientApp app, ClientCtrl controller) throws RemoteException {
		this.mApp = app;
		this.mController = controller;
		initGUI();
	}

	private void initGUI() throws RemoteException {
		// 1. -TODO- Init gui here

		// 2. -TODO- Collect playerName

		// 3. -TODO- login
		mController.login("");

		// 4. -TODO- Register some callbacks for Fly position updated with
		// ClientController. Note : Callback interface not written
		
		// 5. Run the game. Look for more functions in Client controller
		// Note : View doesn't have access to server stubs and doesn't maintain any
		// game state info except those required for UI display

	}

}
