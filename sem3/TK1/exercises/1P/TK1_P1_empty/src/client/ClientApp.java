package client;

import java.rmi.RemoteException;

import common.IGameServer;

/**
 * This is the entry point for client application.
 * 
 * Functions: <br/>
 * 1. Lookup and fetch ServerCtrl from Registry <br/>
 * 2. Create an instance of the ClientCtrl for later use <br/>
 * 3. Create an instance of ClientView and take username <br/>
 * 4. Use the above inside inside ClientView to login using ClientCtrl <br/>
 * 5. Rest of the game
 * 
 * @author praveen
 */
public class ClientApp {

	public ClientApp() {
	}

	public static void main(String[] args) throws RemoteException{
		// Init app object
		ClientApp clientApp = new ClientApp();

		// Get server control object from RMI registry
		IGameServer server = null; // -TODO-

		// Initiate the client controller
		ClientCtrl clientCtrl = new ClientCtrl(server);

		// Initiate the view - GUI, of the client and the game starts, NOW!
		new ClientView(clientApp, clientCtrl);
	}

}
