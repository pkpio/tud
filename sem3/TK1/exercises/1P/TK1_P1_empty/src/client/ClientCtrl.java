package client;

import java.rmi.RemoteException;

import common.IGameClient;
import common.IGameServer;

/**
 * Implementation of client controls which includes those functions exposed by
 * IGameClient and other methods that are required for view<-->controller
 * communication
 * 
 * -- TODO -- Add more methods as required for the view
 * 
 * @author praveen
 */
public class ClientCtrl implements IGameClient {
	IGameServer mServer;
	String mPlayerName;

	/**
	 * Creates an instance of the Client controller. This implements IGameClient
	 * that will be used at login.
	 * 
	 * @param server
	 *            An instance of the IGameServer object for RPCs between client
	 *            and server
	 */
	public ClientCtrl(IGameServer server) {
		this.mServer = server;
	}

	/**
	 * Called by the server to notify that fly on UI is hunted - either by the
	 * current user or someone else. The call back should behave identically in
	 * both cases
	 * 
	 * @param playerName
	 *            Name of the player who hunted the last fly
	 * @param newPoints
	 *            New points of the player who hunted the last fly
	 * @throws RemoteException
	 */
	@Override
	public void recieveFlyHunted(String playerName, int newPoints) throws RemoteException {
		// TODO Auto-generated method stub
	}

	@Override
	/**
	 * called by the server to notify about the new fly position - because the
	 * one on the UI has been hunted by someone
	 * 
	 * @param x
	 *            New x-position of the fly
	 * @param y
	 *            New y-position of the fly
	 * @throws RemoteException
	 */
	public void recieveFlyPosition(int x, int y) throws RemoteException {
		// TODO Auto-generated method stub
	}

	/**
	 * Login with given playerName.
	 * 
	 * @param playerName
	 *            Player name. Will be persistent inside the controller.
	 * @throws RemoteException
	 */
	public void login(String playerName) throws RemoteException {
		this.mPlayerName = playerName;
		mServer.login(playerName, this);
	}

	/**
	 * The current fly has been hunted by the user of this client
	 * 
	 * @throws RemoteException
	 */
	public void huntFly() throws RemoteException {
		mServer.huntFly(mPlayerName);
	}

}
