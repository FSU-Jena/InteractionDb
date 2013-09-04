package edu.fsuj.csb.reactionnetworks.database;

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.rmi.AlreadyBoundException;
import java.rmi.UnexpectedException;
import java.sql.Connection;
import java.sql.DriverManager;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.Statement;
import java.text.SimpleDateFormat;
import java.util.Collection;
import java.util.Date;
import java.util.GregorianCalendar;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;
import java.util.Stack;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.UnknownFormatConversionException;
import java.util.Vector;
import java.util.zip.DataFormatException;

import javax.naming.NameNotFoundException;
import javax.swing.JOptionPane;

import edu.fsuj.csb.tools.configuration.Configuration;
import edu.fsuj.csb.tools.newtork.pagefetcher.PageFetcher;
import edu.fsuj.csb.tools.organisms.Formula;
import edu.fsuj.csb.tools.organisms.Reaction;
import edu.fsuj.csb.tools.urn.URN;
import edu.fsuj.csb.tools.urn.miriam.CasUrn;
import edu.fsuj.csb.tools.urn.miriam.ChEBIUrn;
import edu.fsuj.csb.tools.urn.miriam.DrugBankUrn;
import edu.fsuj.csb.tools.urn.miriam.GlycomeDBurn;
import edu.fsuj.csb.tools.urn.miriam.JcsdUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggCompoundUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggDrugUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggEDrugUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggGlycanUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggReactionUrn;
import edu.fsuj.csb.tools.urn.miriam.KeggUrn;
import edu.fsuj.csb.tools.urn.miriam.KnapsackUrn;
import edu.fsuj.csb.tools.urn.miriam.LipidBankUrn;
import edu.fsuj.csb.tools.urn.miriam.LipidMapsUrn;
import edu.fsuj.csb.tools.urn.miriam.MiriamUrn;
import edu.fsuj.csb.tools.urn.miriam.PubChemSubstanceUrn;
import edu.fsuj.csb.tools.urn.miriam.threeDMetUrn;
import edu.fsuj.csb.tools.xml.NoTokenException;
import edu.fsuj.csb.tools.xml.ObjectComparator;
import edu.fsuj.csb.tools.xml.Tools;
import edu.fsuj.csb.tools.xml.XMLReader;
import edu.fsuj.csb.tools.xml.XmlToken;

//*********** basic methods **********************

/**
 * this class encapsulates the database connection to the database containing the organism data
 * 
 * @author Stephan Richter
 * 
 */
public class InteractionDB {
	private static String dbDriver = "com.mysql.jdbc.Driver";
	/** the following 4 values define defaults for database configuration.
	 * Do not alter these, instead alter ~/.config/InteractionDB/database.config */
	private static String defaultDbHost = "localhost";
	private static String defaultDbUserName = "client";
	private static String defaultDbPassword = "interaction";
	private static String defaultDbName = "interactiondb";
	
	private static boolean testMode = false;
	
	private static Connection connection = null;
	private static TreeMap<String, TreeSet<String>> unificationRules;
	private static TreeMap<URL,Formula> formulaMap=new TreeMap<URL, Formula>(ObjectComparator.get());
	private static TreeSet<String> unresolvedAbbrevations=Tools.StringSet();
	private static long lastConnectionAccess=0;
	private static Configuration configuration;
	
	public final static int COMPARTMENT_GROUP = 1;
	public static final int COMPARTMENT = 2;
	public static final int PATHWAY = 3;
	public static final int SUBSTANCE = 4;
	public static final int ENZYME = 5;
	public static final int REACTION = 6;
	private static final int DEASSIGN = -1;
	private static final int ASSIGN_TO_NEW = 0;
	private static final int ASSIGN_TO_OLD = 1;

	/**
	 * returns the type name of the given type id
	 * 
	 * @param type
	 * @return
	 */
	private static String nameForType(int type) {
		switch (type) {
		case 1:
			return "COMPARTMENT_GROUP";
		case 2:
			return "COMPARTMENT";
		case 3:
			return "PATHWAY";
		case 4:
			return "SUBSTANCE";
		case 5:
			return "ENZYME";
		case 6:
			return "REACTION";
		}
		return "UNKNOWN ENTITY TYPE";
	}

	public static void setDBName(String db) {
		defaultDbName = db;
	}

	/**
	 * tries to establish a connection to the database
	 * 
	 * @return the connection handle
	 * @throws SQLException
	 * @throws IOException 
	 */
	private static Connection connectDB() throws SQLException, IOException {
		if (connection!=null) try {
			Tools.indent("closing outdated Connection");
			Thread.sleep(2000);
			connection.close();
		} catch (SQLException e) {			
		} catch (InterruptedException e) {}
		
		Tools.indent("Connecting to database " + getDBName() + " on " + getDBHost() + "..."); // Ausgabe auf der Konsole
		try {
			Class.forName(dbDriver).newInstance(); // Erzeugt eine neue Instanz des Datenbanktreibers
			Connection result = DriverManager.getConnection("jdbc:mysql://" + getDBHost() + "/", getDBUser(), getDBPassword()); // stellt die Verbindung über den Treiber her
			result.createStatement().execute("USE " + getDBName());
			Tools.indent("ok."); // Ausgabe auf der Konsole
			return result; // übergibt die geöffnete Verbindung an die aufrufende Methode
		} catch (Exception e) {
			throw new SQLException("Unable to connect to database ("+getDBName()+" on "+getDBHost()+")!");
		}
	}

	private static String getDBPassword() throws IOException {
		return configuration().get("dbpassword",defaultDbPassword);
  }



	private static Configuration configuration() throws IOException {
		if (configuration==null) configuration=new Configuration("InteractionDB");
	  return configuration;
  }

	private static String getDBUser() throws IOException {
		return configuration().get("dbuser",defaultDbUserName);  
  }

	private static String getDBHost() throws IOException {		
		String host=configuration().get("host",defaultDbHost);
		if (configuration().containsKey("dbport")) host+=":"+configuration().get("dbport");
		return host;
	}

	private static String getDBName() throws IOException {		
	  return configuration().get("dbname",defaultDbName);
  }
	







	/**
	 * tries to connect to the interaction database and return the connections
	 * 
	 * @return the database connection, after it has been established
	 * @throws SQLException
	 * @throws IOException if config file can not be read
	 */
	private static Connection databaseConnection() throws SQLException, IOException {
		if (connection == null || connection.isClosed() || connectionOutDated()) connection = connectDB();		
		lastConnectionAccess = new GregorianCalendar().getTimeInMillis()/1000;
		return connection;
	}

	private static boolean connectionOutDated() {
		long time=new GregorianCalendar().getTimeInMillis()/1000;
		return (time-lastConnectionAccess)>3600;
  }

	/**
	 * starts a new database statement. a new database connection is established, if needed
	 * 
	 * @return the database statement object
	 * @throws SQLException
	 * @throws IOException if the db config file can not be read
	 */
	public static Statement createStatement() throws SQLException, IOException {
		return databaseConnection().createStatement();
	}

	/**
	 * execute a certain database query
	 * 
	 * @param query
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static void execute(String query) throws SQLException, IOException  {
		if (testMode) return;
		try {
			Statement st = createStatement();			
			st.execute(query);
			st.close();
		} catch (SQLException e) {
			if (e.getMessage().contains("Communication link failure")) try {
					resetConnection();
					Statement st = createStatement();			
					st.execute(query);
					st.close();
			} catch (SQLException e2){
				throw new SQLException(e.getMessage()+" : "+query);
			}
		}
		Tools.indent(query);
	}

	private static void resetConnection() {
	  try {
	    connection.close();
    } catch (SQLException e) {}
	  connection=null;	  
  }

	/**
	 * converts a collection to a string in the format of the databses, e.g "(object1, object2, object 3)"
	 * 
	 * @param c the collection to be stringified
	 * @return the string representation of this collection, surrounded by normal brackets
	 */
	@SuppressWarnings("rawtypes")
	public static String setToDBset(Collection c) {
		if (c.isEmpty()) return "()";
		Object firstElement=c.iterator().next();
		String result=c.toString();
		if (firstElement.getClass()==Integer.class){
			result=result.replace("[", "(").replace("]", ")");
		} else {
			result=result.replace("[", "('").replace("]", "')").replace(", ", "', '");
		}
		return result;
	}

	/**
	 * creates a tick-escaped string for database requests
	 * 
	 * @param o the object, whose string shall be escaped
	 * @return the escaped string representation of the object
	 */
	public static String dbString(Object o) {
		if (o==null) return "NULL";
		return "'" + o.toString().replace("'", "\\'") + "'";
	}

	/**
	 * create primary key entry
	 * 
	 * @param column
	 * @return
	 */
	private static String key(String column) {
		return column + " INT NOT NULL AUTO_INCREMENT PRIMARY KEY";
	}

	/**
	 * makes sure, that the database tables exist
	 * 
	 * @throws SQLException if sql problems occur
	 * @throws IOException 
	 */
	public static void checkTables() throws SQLException, IOException {
		Tools.startMethod("checktables()");
		if (testMode){
			Tools.endMethod();
			return;
		}
		Statement st = createStatement();
		Tools.indent("Assuring existence of required tables...");
		Vector<String> queries = new Vector<String>();
		queries.add("CREATE TABLE names (" + key("nid") + ", name TEXT NOT NULL)");
		queries.add("CREATE TABLE urls (" + key("lid") + ", url TEXT NOT NULL)");

		queries.add("CREATE TABLE ids (" + key("id") + ",type INT NOT NULL REFERENCES names(nid))");
		queries.add("CREATE TABLE id_ranges (nid INT PRIMARY KEY REFERENCES names(nid), min INT NOT NULL REFERENCES ids(id), max INT NOT NULL REFERENCES ids(id))");
		
		queries.add("CREATE TABLE id_names (id INT NOT NULL REFERENCES ids(id), nid INT NOT NULL REFERENCES names(nid), lid INT NOT NULL REFERENCES urls(lid), PRIMARY KEY(id,nid,lid))");
		queries.add("CREATE TABLE compartments (id INT NOT NULL PRIMARY KEY REFERENCES ids(id),groups INT NOT NULL REFERENCES names(nid))");
		queries.add("CREATE TABLE urns (" + key("uid") + ", id INT REFERENCES ids(id), urn TEXT NOT NULL)");
		queries.add("CREATE TABLE reactions (id INT NOT NULL PRIMARY KEY REFERENCES ids(id), spontan BOOL DEFAULT 0)");
		queries.add("CREATE TABLE substances (id INT NOT NULL PRIMARY KEY REFERENCES ids(id),formula TEXT)");

		queries.add("CREATE TABLE substrates (sid INT NOT NULL REFERENCES substances(id),rid INT NOT NULL REFERENCES reactions(id),stoich FLOAT NOT NULL,PRIMARY KEY(sid,rid))");
		queries.add("CREATE TABLE products  (sid INT NOT NULL REFERENCES substances(id),rid INT NOT NULL REFERENCES reactions(id),stoich FLOAT NOT NULL,PRIMARY KEY(sid,rid))");
		queries.add("CREATE TABLE reaction_directions (rid INT NOT NULL REFERENCES reactions(id), cid INT NOT NULL REFERENCES compartments(id), forward BOOLEAN, backward BOOLEAN, PRIMARY KEY(rid,cid))");
		queries.add("CREATE TABLE enzymes (id INT NOT NULL PRIMARY KEY REFERENCES ids(id),ec TEXT,substance BOOLEAN DEFAULT FALSE)");
		queries.add("CREATE TABLE compartment_pathways (cid INT NOT NULL REFERENCES compartments(id),pid INT NOT NULL REFERENCES ids(id),PRIMARY KEY (cid,pid))");
		queries.add("CREATE TABLE hierarchy (contained INT NOT NULL REFERENCES compartments(id),container INT NOT NULL REFERENCES compartments(id),PRIMARY KEY(contained,container))");
		queries.add("CREATE TABLE urn_urls (uid INT NOT NULL REFERENCES urns(uid), lid INT NOT NULL REFERENCES urls(lid), PRIMARY KEY (uid,lid))");

		queries.add("CREATE TABLE reaction_enzymes (rid INT NOT NULL REFERENCES reactions(id),eid INT NOT NULL REFERENCES enzymes(id),PRIMARY KEY(rid,eid))");
		queries.add("CREATE TABLE enzymes_compartments (cid INT NOT NULL REFERENCES compartments(id),eid INT NOT NULL REFERENCES enzymes(id),PRIMARY KEY (cid,eid))");
		queries.add("CREATE TABLE dates ("+key("did")+",date DATE NOT NULL, description TEXT NOT NULL)");
		queries.add("CREATE TABLE decisions (keyphrase VARCHAR(500) NOT NULL PRIMARY KEY, value INT, autogenerated BOOL DEFAULT 0) CHARACTER SET latin1");
		queries.add("CREATE TABLE abbrevations (abbr VARCHAR(32) PRIMARY KEY,id INTEGER NOT NULL REFERENCES substances(id))");
		//queries.add("CREATE TABLE replacements (phrase VARCHAR(500) NOT NULL PRIMARY KEY, replacement VARCHAR(500))");
		
		
		for (int i=1; i<7; i++) queries.add("INSERT INTO names VALUES ("+i+","+dbString(nameForType(i))+")");

		String query = null;
		for (Iterator<String> it = queries.iterator(); it.hasNext();) {
			try {
				query = it.next();
				st.execute(query);
				Tools.indent(query);
			} catch (SQLException e) {
				if (e.getMessage().contains("already exists")) continue;
				if (e.getMessage().contains("Duplicate key")) continue;
				System.err.println(query);
				throw e;
			}
		}
		st.close();
		Tools.indent("done.");
		Tools.endMethod();
	}

	public static Integer getOrCreateEntry(String tableName, String idName, String keyName, Object key) throws SQLException, IOException {
		Tools.startMethod("getOrCreateEntry(table='"+tableName+"', id column='"+idName+"', key column='"+ keyName+"', key value='"+ key+"')");
		if (key==null) return null;
		String query = "SELECT " + idName + " FROM " + tableName + " WHERE " + keyName + "=" + dbString(key);
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			int result = 0;
			if (rs.next()) {
				result = rs.getInt(1);
				rs.close();
				st.close();
				Tools.endMethod(result);
				return result;
			}
			rs.close();
			rs=null;
			int id = 0;
			if (!testMode){
				query = "INSERT INTO " + tableName + "("+keyName+") VALUES(" + dbString(key) + ")";
				st.execute(query, Statement.RETURN_GENERATED_KEYS);			
				Tools.indent(query);
				rs = st.getGeneratedKeys();
				if (rs.next()) id = rs.getInt(1);
				rs.close();
			}
			st.close();
			Tools.endMethod(id);
			return id;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}

//*************** basic methods ********************************	
	
//**** names *******************************
	
	/**
	 * tries to read the nid of the given name. if this name is not in the database, it will be inserted
	 * 
	 * @param name a entity name
	 * @return the id related to the name
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static int getOrCreateNid(String name) throws SQLException, IOException {
		Tools.startMethod("getOrCreateNid("+name+")");
		int result = getOrCreateEntry("names", "nid", "name", name);
		Tools.endMethod(result);
		return result;
	}
	
	/**
	 * add a name to the given urn
	 * 
	 * @param urn
	 * @param name
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static void addName(int id, String name, URL source) throws SQLException, IOException {
		Tools.startMethod("addName(id="+id+", '"+name+"', "+source+")");
		int nid = getOrCreateNid(name);
		Integer lid = getOrCreateUrlId(source);
		try {
			execute("INSERT INTO id_names VALUES(" + id + ", " + nid + ", "+lid+")");
		} catch (SQLException e) {
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod();
	}

	/**
	 * add a bunch of names to a given urn
	 * 
	 * @param urn
	 * @param names
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static void addNames(int id, Collection<String> names, URL source) throws SQLException, IOException {
		Tools.startMethod("addNames(id="+id+", "+names+", "+source+")");
		int lid = getOrCreateUrlId(source);
		Statement st = createStatement();
		for (Iterator<String> it = names.iterator(); it.hasNext();) {
			int nid = getOrCreateNid(it.next());
			try {
				execute("INSERT INTO id_names VALUES("+id +", " +nid + ","+lid+")");
			} catch (SQLException e){
				if (e.getMessage().contains("Duplicate key")) continue;
			}
		}
		st.close();
		Tools.endMethod();
	}
	
	/**
	 * tries to get all names for the url
	 * 
	 * @param url
	 * @return
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<String> getNames(URL url) throws SQLException, IOException {
		int lid = getOrCreateUrlId(url);
		TreeSet<String> result = Tools.StringSet();
		String query = "SELECT DISTINCT name FROM urls NATURAL JOIN id_names NATURAL JOIN names WHERE lid=" + lid;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next())	result.add(rs.getString(1));
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		return result;
	}
	
	/**
	 * request the names belonging to a certain urn
	 * @param urn
	 * @return
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<String> getNames(URN urn) throws SQLException, IOException{
		Tools.startMethod("getNames("+urn+")");
		int uid=getOrCreateUid(urn);
		TreeSet<String> result = Tools.StringSet();
		String query = "SELECT DISTINCT name FROM urns NATURAL JOIN id_names NATURAL JOIN names WHERE uid="+uid;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next())	result.add(rs.getString(1));
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}
	
	/**
	 * request the names belonging to a certain urn
	 * @param urn
	 * @return
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<String> getNames(int id) throws SQLException, IOException{
		Tools.startMethod("getNames("+id+")");
		TreeSet<String> result = Tools.StringSet();
		String query = "SELECT DISTINCT name FROM id_names NATURAL JOIN names WHERE id="+id;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next())	result.add(rs.getString(1));
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}
	
	public static String getName(int nid) throws SQLException, IOException{
		Tools.startMethod("getName(nid="+nid+")");
		String query="SELECT name FROM names WHERE nid="+nid;
		String result=null;
		try {
		Statement st=createStatement();
		ResultSet rs=st.executeQuery(query);
		if (rs.next()) result=rs.getString(1);
		rs.close();
		st.close();
		} catch (SQLException e){
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
		
	}
		
//******** names **********************************************

//******** urls *****************************************
	
	/**
	 * tries to read the urlid for the given url. if no such url is in the database, it will be inserted and it's id will be returned
	 * 
	 * @param url the urls, for which the url id shall be given
	 * @return the urlid for the given url
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static Integer getOrCreateUrlId(URL url) throws SQLException, IOException {
		Tools.startMethod("getOrCreateUrlId("+url+")");
		Integer result=getOrCreateEntry("urls", "lid", "url", url);
		Tools.endMethod("return "+result);
		return result;
	}

	/**
	 * try to get all urls referencing a certain urn
	 * 
	 * @param urn
	 * @return
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<URL> getReferencingURLs(URN urn) throws SQLException, IOException {
		int uid = getOrCreateUid(urn);
		TreeSet<URL> result = Tools.URLSet();
		String query = "SELECT url FROM urn_urls NATURAL JOIN urls WHERE uid=" + uid;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next()) {
				try {
					result.add(new URL(rs.getString(1)));
				} catch (MalformedURLException e) {
					System.err.println(query);
					System.err.println(e.getMessage());
				}
			}
			st.close();
			rs.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		return result;
	}
	
	public static Vector<URL> getReferencingURLs(int id) throws SQLException, IOException {
		Tools.startMethod("getReferencingURLs("+id+")");
		Vector<URL> result = new Vector<URL>();
		String query = "SELECT DISTINCT url FROM ids NATURAL JOIN urns NATURAL JOIN urn_urls NATURAL JOIN urls WHERE id ="+id;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next()) {
				try {
					result.add(new URL(rs.getString(1)));
				} catch (MalformedURLException e) {
					System.err.println(query);
					System.err.println(e.getMessage());
				}
			}
			st.close();
			rs.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}
	
	/**
	 * return the urls belonging to an urn by resolving it usign the miriam registry
	 * @param urn the urn, for whose urls we are looking
	 * @return the associated urls
	 * @throws MalformedURLException
	 */
	public static Set<URL> getUrls(URN urn) throws MalformedURLException{
		return urn.urls();
	}
	
	/**
	 * collects all urls of urns related to this id and returns them
	 * @param id the id, whose urls are requested
	 * @return the set of urls related to this entry id
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<URL> getUrls(int id) throws SQLException, IOException {
		Tools.startMethod("getUrls("+id+")");
		Vector<URN> urns = getURNsFor(id);
		TreeSet<URL> urls = Tools.URLSet();
		for (Iterator<URN> it = urns.iterator(); it.hasNext();) {
			URN urn = it.next();
			urls.addAll(urn.urls());
		}
		Tools.endMethod(urls);
		return urls;
	}

//******* urls **********************************************
	
//******* urns **********************************************
	/**
	 * tries to read the uid of the given urn. If this name is not in the database, it will be inserted
	 * 
	 * @param urn the urn, for which the uid is requested
	 * @return the id of the urn
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static int getOrCreateUid(URN urn) throws SQLException, IOException {
		Tools.startMethod("getOrCreateUid("+urn+")");
		int result = getOrCreateEntry("urns", "uid", "urn", urn);
		Tools.endMethod(result);
		return result;
	}

	/**
	 * get the urns referenced by a certain url
	 * 
	 * @param url
	 * @return
	 * @throws SQLException
	 * @throws DataFormatException
	 * @throws IOException 
	 */
	public static TreeSet<URN> getReferencedUrns(URL url) throws SQLException, DataFormatException, IOException {
		Tools.startMethod("getReferencedUrns("+url+")");
		int lid = getOrCreateUrlId(url);
		TreeSet<URN> result = new TreeSet<URN>(ObjectComparator.get());
		String query = "SELECT urn FROM urn_urls NATURAL JOIN urns WHERE lid=" + lid;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next()) result.add(new MiriamUrn(rs.getString(1)));
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}
	
	/**
	 * try to get the urns of a given id
	 * 
	 * @param id
	 * @return the set of urns associated with the given id
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static TreeSet<Integer> getUIDsFor(int id) throws SQLException, IOException {
		Tools.startMethod("getUIDsFor("+id+")");
		TreeSet<Integer> result = new TreeSet<Integer>(ObjectComparator.get());
		String query = "SELECT uid FROM urns WHERE id=" + id;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next()) {
				int dummy=rs.getInt(1);
				if (dummy!=0)	result.add(dummy);
			}
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}

	
	/**
	 * try to get the urns of a given id
	 * 
	 * @param id
	 * @return the set of urns associated with the given id
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static Vector<URN> getURNsFor(int id) throws SQLException, IOException {
		Tools.startMethod("getURNsFor("+id+")");
		Vector<URN> result = new Vector<URN>();
		String query = "SELECT urn FROM urns WHERE id=" + id;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			Tools.indent(query);
			while (rs.next()) {
				try {
					result.add(new MiriamUrn(rs.getString(1)));
				} catch (DataFormatException e) {
					System.err.println(query);
					System.err.println(e.getMessage());
				}
			}
			rs.close();
			st.close();
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
		Tools.endMethod(result);
		return result;
	}

	public static TreeSet<Integer> readUidsFor(Collection<URN> urns) throws SQLException, IOException{
		Tools.startMethod("readUidsFor("+urns+")");
		String query="SELECT uid FROM urns WHERE urn IN "+setToDBset(urns);		
		try {
	    Statement st=createStatement();
	    ResultSet rs=st.executeQuery(query);
	    Tools.indent(query);
	    TreeSet<Integer> result=new TreeSet<Integer>();
			while (rs.next()) result.add(rs.getInt(1));
			Tools.endMethod(result);
	    return result;
    } catch (SQLException e) {
			System.err.println(query);
			throw e;
		}		
	}
//**************** urns ***************************************************
	
//************ component ids *************************************

	public static int newId(int type) throws SQLException, IOException {
		Tools.startMethod("newId(type="+type+")");
		String query = "INSERT INTO ids VALUES(0, " + type + ")";
		try {
			int id = 0;
			if (!testMode){
				Statement st = createStatement();
				st.executeUpdate(query, Statement.RETURN_GENERATED_KEYS);
				Tools.indent(query);
				ResultSet rs = st.getGeneratedKeys();
				if (rs.next()) id = rs.getInt(1);
				rs.close();
				st.close();
			}
			Tools.endMethod(id);
			return id;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}
	
	public static Integer readIdFor(Integer uid) throws SQLException, IOException{
		Tools.startMethod("readIdFor("+uid+")");
		String query="SELECT id FROM urns WHERE uid="+uid;		
		try {
	    Statement st=createStatement();
	    ResultSet rs=st.executeQuery(query);
	    Tools.indent(query);
	    Integer result=null;
	    if (rs.next()) result=rs.getInt(1);
		if (result!=null && result==0) result=null;
	    rs.close();
	    st.close();
		Tools.endMethod(result);
	    return result;
    } catch (SQLException e) {
			System.err.println(query);
			throw e;
		}		
	}
	
	public static Integer readIdFor(URN urn) throws SQLException, IOException {
		Tools.startMethod("readIdFor("+urn+")");
		String query="SELECT id FROM urns WHERE urn="+dbString(urn);		
		try {
	    Statement st=createStatement();
	    ResultSet rs=st.executeQuery(query);
	    Tools.indent(query);
	    Integer result=null;
	    if (rs.next()) result=rs.getInt(1);
			if (result!=null && result==0) result=null;
			Tools.endMethod(result);
	    return result;
    } catch (SQLException e) {
			System.err.println(query);
			throw e;
		}		
	}
	
	public static TreeSet<Integer> readIdsFor(Collection<Integer> uids) throws SQLException, IOException{
		Tools.startMethod("readIdsFor("+uids+")");
    TreeSet<Integer> result=new TreeSet<Integer>();
    if (uids!=null && !uids.isEmpty()){
    	String query="SELECT id FROM urns WHERE uid IN "+setToDBset(uids);		
			try {
	    	Statement st=createStatement();
	    	ResultSet rs=st.executeQuery(query);
	    	Tools.indent(query);
				while (rs.next()) {
					int dummy=rs.getInt(1);
					if (dummy!=0) result.add(dummy);
				}
    	} catch (SQLException e) {
				System.err.println(query);
				throw e;
			}		
    }
		Tools.endMethod(result);
    return result;
	}
	
	public static int getOrCreateIdFor(int uid,int type) throws SQLException, IOException{
		Tools.startMethod("getOrCreateIdFor(uid="+uid+", type="+type+")");
		Integer id=readIdFor(uid);
    if (id==null){
	    id=newId(type);
	    execute("UPDATE urns SET id="+id+" WHERE uid ="+uid);
	  }
		Tools.endMethod(id);
		return id;
	}
	

	public static int getOrCreateIdFor(URN urn,int type) throws SQLException, IOException{
		Tools.startMethod("getOrCreateIdFor("+urn+", "+type+")");
		int id=getOrCreateIdFor(getOrCreateUid(urn),type);
		Tools.endMethod(id);
		return id;
	}	
	
	public static int getOrCreateIdFor(Collection<URN> urns, int type) throws SQLException, NoSuchMethodException, IOException{
		Tools.startMethod("getOrCreateIdFor("+urns+", "+type+")");
		TreeSet<Integer> uids=new TreeSet<Integer>();
		if (urns!=null){
			for (Iterator<URN> it = urns.iterator(); it.hasNext();) uids.add(getOrCreateUid(it.next()));
		}		
		TreeSet<Integer> ids = readIdsFor(uids);
		if (ids.isEmpty()){
			int id=newId(type);
			if (!uids.isEmpty()) execute("UPDATE urns SET id="+id+" WHERE uid IN "+setToDBset(uids));
			Tools.endMethod(id);
			return id;
		}
		if (ids.size()>1){
			// we have at least two of the urns in the database, and they point to different ids
			int result=mergeIds(ids);
			Tools.endMethod("return "+result);
			execute("UPDATE urns SET id="+result+" WHERE uid in "+setToDBset(uids)); // sollte bei allen relevanten uids die ids richtig setzen
			return result; 
		} else if (uids.size()>1){ // at this point, we have one id, but several uids, which may not all point to the id
			execute("UPDATE urns SET id="+ids.first()+" WHERE uid in "+setToDBset(uids));
		}
		
		Tools.endMethod("return "+ids.first());
		return ids.first();
	}

	private static Integer mergeIds(TreeSet<Integer> ids) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("mergeIds("+ids+")");
		int type=getTypesOf(ids);
		Iterator<Integer> it = ids.iterator();
		Integer remaining = it.next();
		while (it.hasNext()) mergeIds(remaining, it.next(),type);
		Tools.endMethod(remaining);
		return remaining;
  }

	private static int getTypesOf(TreeSet<Integer> ids) throws SQLException, IOException {
	  Tools.startMethod("unequalTypesOf("+ids+")");
	  String query="SELECT DISTINCT type FROM ids WHERE id IN "+setToDBset(ids);
	  try{
	  	Statement st=createStatement();
	  	ResultSet rs=st.executeQuery(query);
	  	String error=null;
	  	int result=0;
	  	if (rs.next()){
	  		result=rs.getInt(1);
		  	if (rs.next()) error="Found more than one type for ids ("+ids+")!";
		 	} else error="Found NO type for ids ("+ids+")!";	  	
	  	rs.close();
	  	st.close();
	  	if (error!=null && !testMode) throw new UnexpectedException(error);
	  	Tools.endMethod(result);
	  	return result;
		} catch (SQLException e){
			System.err.println(query);
			throw e;
		}
  }

	private static void mergeIds(Integer remaining, int merged,int type) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("mergeIds("+remaining+", "+merged+", type="+type+")");
		if (mergingAllowed(remaining,merged)){
			switch (type){
			case SUBSTANCE: mergeSubstances(remaining,merged); break;
			default:
				throw new NoSuchMethodException("unification of entities of " + nameForType(type));
			}
			execute("UPDATE urns SET id="+remaining+" WHERE id="+merged);
			try {
				execute("UPDATE id_names SET id="+remaining+" WHERE id="+merged);
			} catch (SQLException e){
				if (!e.getMessage().contains("Duplicate entry")) throw e;
			}
			execute("DELETE FROM id_names WHERE id="+merged);
		}
		Tools.endMethod();
  }
	
	private static boolean mergingAllowed(int remaining, int merged) throws SQLException, IOException {
		Tools.startMethod("mergingAllowed("+remaining+", "+merged+")");
		Vector<URN> urns1 = getURNsFor(remaining);
		Vector<URN> urns2 = getURNsFor(merged);
		
		
		TreeMap<String, TreeSet<String>> rules;
    try {
	    rules = loadUnificationRules();
    } catch (Exception e) {
    	e.printStackTrace();
    	Tools.endMethod(true);
    	return true;
    }
    for (Iterator<URN> it1 = urns1.iterator(); it1.hasNext();){
    	URN urn = it1.next();
    	TreeSet<String> forbiddenSet = rules.get(urn);
    	if (forbiddenSet!=null){
    		for (Iterator<URN> it2 = urns2.iterator(); it2.hasNext();){
    			if (forbiddenSet.contains(it2.next())) {
    				Tools.endMethod(false);
    				return false;
    			}
    		}
    	}
    }
    Tools.endMethod(true);
		return true;
  }
	
	/**
	 * @return a map from urn strings to sets of other urn strings which may not be merged with the first one
	 * @throws MalformedURLException
	 * @throws IOException
	 * @throws NoTokenException
	 */
	private static TreeMap<String,TreeSet<String>> loadUnificationRules() throws MalformedURLException, IOException, NoTokenException {
		if (unificationRules==null){
			unificationRules=new TreeMap<String, TreeSet<String>>(ObjectComparator.get());			
			XMLReader xr = new XMLReader(getUnificationRulesFilename());
			XmlToken rules=xr.readToken();
			if (rules.instanceOf("urnRules")){
				for (XmlToken rule: rules.subtokens()){
					if (rule.instanceOf("denyUnification")){
						String urn1=rule.getValue("urn1");
						String urn2=rule.getValue("urn2");
						if (!unificationRules.containsKey(urn1)) unificationRules.put(urn1, Tools.StringSet());
						unificationRules.get(urn1).add(urn2);
					}
				}
			}
		}
	  
		return unificationRules;
  }

	private static String getUnificationRulesFilename() throws IOException {
	  return configuration().get("unificationRules", System.getProperty("user.home")+"/workspace/InteractionDb/urnRules.xml");
  }

	private static void mergeSubstances(Integer keptId, int mergedId) throws SQLException, IOException {
		Tools.startMethod("mergeSubstances("+keptId+", "+mergedId+")");
		
		uniteReactants("products",keptId,mergedId);
		uniteReactants("substrates",keptId,mergedId);
		
		execute("DELETE FROM substances WHERE id="+mergedId);
		Tools.endMethod();
	}

	private static void uniteReactants(String table, Integer keptId, int mergedId) throws SQLException, IOException {
		Tools.startMethod("uniteReactants("+table+", "+mergedId+" ← "+keptId+")");
		String query="SELECT rid,stoich FROM "+table+" WHERE sid="+mergedId; // select Reactions with obsolete agent
		
		try{
			Statement st=createStatement();
			Tools.indent(query);
			ResultSet rs=st.executeQuery(query);
			TreeMap<Integer,Double> reactionsWithObsoleteReactant=new TreeMap<Integer, Double>();
			while (rs.next()) reactionsWithObsoleteReactant.put(rs.getInt(1),rs.getDouble(2)); // collect rids respective stoich for obsolete substances
			rs.close();
		
			for (Iterator<Entry<Integer, Double>> rit = reactionsWithObsoleteReactant.entrySet().iterator(); rit.hasNext();){
				Entry<Integer, Double> entry = rit.next();
				int rid=entry.getKey();
				double obsoleteStoich=entry.getValue();
			
				query="SELECT stoich FROM "+table+" WHERE rid="+rid+" AND sid="+keptId;
				Tools.indent(query);
				rs=st.executeQuery(query);
				
				if (rs.next()){ // both, the kept and the merged id have an entry in this reaction
					double newStoich=obsoleteStoich+rs.getDouble(1);
					rs.close();
				
					query="UPDATE "+table+" SET stoich = "+newStoich+" WHERE rid="+rid+" AND sid="+keptId; // update stoichiometric coefficient of kept agent
					Tools.indent(query);
					execute(query);
				
					// entry for merged id will be removed after loop				
				} else { // only the kept id have en entry in this reaction term
					query="UPDATE "+table+" SET sid="+keptId+" WHERE rid="+rid+" AND sid="+mergedId;
					Tools.indent(query);
					execute(query);
				}				
			}
			st.close();
			if (!reactionsWithObsoleteReactant.isEmpty()){
				query="DELETE FROM "+table+" WHERE sid="+mergedId; // remove entries of obsolete agent from table
				Tools.indent(query);
				execute(query);
			}
		} catch (SQLException e){
			System.err.println(query);
			throw	e;
		}
		Tools.endMethod();
  }

	public static Integer getLastID() throws SQLException, IOException {
		Tools.startMethod("getLastId()");
		String query="SELECT MAX(id) FROM ids";
		try {
			Statement st=createStatement();
			ResultSet rs=st.executeQuery(query);
			rs.next();
			int result=rs.getInt(1);
			rs.close();
			st.close();
			Tools.endMethod(result);
			return result;
		} catch (SQLException e){
			System.err.println(query);
			throw e;
		}
  }

//******** component ids *****************************************
	
//******** references *********************************
	
	public static void insertReference(int lid, int uid) throws SQLException, IOException{
		Tools.startMethod("insertReference(lid="+lid+", uid="+uid+")");
		try {
			execute("INSERT INTO urn_urls VALUES ("+uid+", "+lid+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod();
	}

	public static void insertReference(URL url,URN urn) throws SQLException, IOException{
		Tools.startMethod("insertReference("+url+", "+urn+")");
		int urlid=getOrCreateUrlId(url);
		int uid=getOrCreateUid(urn);
		insertReference(urlid, uid);
		Tools.endMethod();
	}
	
	public static void insertReferences(URL url,Collection<URN> urns) throws SQLException, IOException{
		Tools.startMethod("insertReferences("+url+", "+urns+")");
		int urlid=getOrCreateUrlId(url);
		for (Iterator<URN> it = urns.iterator(); it.hasNext();){
			int uid=getOrCreateUid(it.next());
			insertReference(urlid, uid);			
		}
		Tools.endMethod();
	}
	
	public static void linkPathway(Integer pid, Integer cid) throws SQLException, IOException {
		Tools.startMethod("linkPathway(pid="+pid+", cid="+cid+")");
		execute("INSERT INTO compartment_pathways VALUES(" + cid + ", " + pid + ")");
		Tools.endMethod();
  }

	public static void linkEnzymesToReaction(int rid, TreeSet<String> ecNumbers) throws SQLException, IOException {
		TreeSet<Integer> eids = readEnzymeIds(ecNumbers);
		for (Iterator<Integer> eid = eids.iterator(); eid.hasNext();){
			execute("INSERT INTO reaction_enzymes VALUES (" + rid + "," + eid.next() + ")");
		}
  }
	
	public static void linkOrganismsToEnzyme(TreeSet<Integer> cids, int eid) throws SQLException, IOException {
		Tools.startMethod("linkOrganismsToEnzyme(cids="+cids+", eid="+eid+")");
		if (testMode) return;
		String query=null;
		try {
			Statement st = createStatement();			
			for (Iterator<Integer> cid = cids.iterator();cid.hasNext();) {
				query="INSERT INTO enzymes_compartments VALUES("+cid.next()+", "+eid+")";
				st.execute(query);
			}
			st.close();
		} catch (SQLException e) {
			if (e.getMessage().contains("Communication link failure"))
				try {
					resetConnection();
					Statement st = createStatement();			
					st.execute(query);
					st.close();
				} catch (SQLException e2){
					throw new SQLException(e.getMessage()+" : "+query);
				}
		}		
		Tools.endMethod();
  }

//********** references *************************************************
	
//******** organism components ***********************************
	
	private static int createBaseComponent(int type, URL source, Collection<URN>urns, Collection<String> names) throws SQLException, NoSuchMethodException, IOException{
		Tools.startMethod("createBaseComponent("+nameForType(type)+", "+source+", "+urns+", "+names+")");
		int id = getOrCreateIdFor(urns, type);
		addNames(id, names, source);
		if (urns!=null && !urns.isEmpty())	insertReferences(source, urns);
		Tools.endMethod(id);
		return id;
	}
	




	private static int createBaseComponent(int type, URL source, URN urn, Collection<String> names) throws SQLException, IOException{
		Tools.startMethod("createBaseComponent("+nameForType(type)+", "+source+", "+urn+", "+names+")");
		int id = getOrCreateIdFor(urn, type);
		addNames(id,names,source);
		if (urn!=null) insertReference(source, urn);
		Tools.endMethod(id);
		return id;
	}
	
	private static int createBaseComponent(int type, URL source, URN urn, String name) throws SQLException, IOException{
		Tools.startMethod("createBaseComponent("+nameForType(type)+", "+source+", "+urn+", '"+name+"')");
		int id = getOrCreateIdFor(urn, type);
		addName(id,name,source);
		if (urn!=null) insertReference(source, urn);
		Tools.endMethod(id);
		return id;
	}
	
	private static int createBaseComponent(int type, URL source, Collection<URN>urns, String name) throws SQLException, NoSuchMethodException, IOException{
		Tools.startMethod("createBaseComponent("+nameForType(type)+", "+source+", "+urns+", '"+name+"')");
		int id = getOrCreateIdFor(urns, type);
		addName(id,name,source);
		if (urns!=null && !urns.isEmpty()) insertReferences(source, urns);
		Tools.endMethod(id);
		return id;
	}
	

 	/**
	 * @param names
	 * @param newFormula
	 * @param linkedUrns
	 * @param sourceOfNewEntry
	 * @throws SQLException
 	 * @throws NoSuchMethodException 
 	 * @throws DataFormatException 
 	 * @throws NoTokenException 
 	 * @throws IOException 
	 */
	public static int createSubstance(Collection<String> names,Formula newFormula,Collection<URN> linkedUrns, URL sourceOfNewEntry) throws SQLException, NoSuchMethodException, DataFormatException, IOException, NoTokenException{
		Tools.startMethod("createSubstance("+names+", "+newFormula+", "+linkedUrns+", "+sourceOfNewEntry+")");
		
		int newId=newId(SUBSTANCE);
		TreeSet<Integer> compatibleIds=new TreeSet<Integer>();
		Vector<URN> collidingURNs=new Vector<URN>();
		compatibleIds.add(newId);
		
		for (URN urnLinkedFromNewEntry : linkedUrns) {

			getOrCreateUid(urnLinkedFromNewEntry);
	    Integer existingId = readIdFor(urnLinkedFromNewEntry);
	    
	    if (existingId != null){ // if there is already an entry for the current urn: check, whether it is compatible
	    	Formula existingFormula = getFormula(existingId);
	    	Tools.indent("existing formula: "+existingFormula);
	    	Tools.indent("new formula: "+newFormula);
	    	if (newFormula==null || existingFormula==null || newFormula.equals(existingFormula)){
	    		compatibleIds.add(existingId); // compatible
	    	} else { // assigned entry has another formula => ask, to which entry the urn shall be assigned
	    		Integer select=askAndAssignUrn(sourceOfNewEntry, urnLinkedFromNewEntry,newId,newFormula,existingId);
	    		if (select!=0) collidingURNs.add(urnLinkedFromNewEntry);
	    	}
	    }
    }
		
		for (URN urn : collidingURNs) linkedUrns.remove(urn);
		
		int id = mergeIds(compatibleIds);
		
		Tools.indent("id   = "+id);
		Tools.indent("urns = "+linkedUrns);
		if (!linkedUrns.isEmpty()){
			TreeSet<Integer> uids = readUidsFor(linkedUrns);
		
			Tools.indent("uids = "+uids);
			
			execute("UPDATE urns SET id="+id+" WHERE uid in "+setToDBset(uids)); // sollte bei allen relevanten uids die ids richtig setzen
		}
		addNames(id, names, sourceOfNewEntry);
		if (linkedUrns!=null && !linkedUrns.isEmpty())	insertReferences(sourceOfNewEntry, linkedUrns);
		
		
		
	 /* TODO:
	  * an dieser Stelle sollte geprüft werden, ob durch die URNs mehrere Substanzen vereint werden.
	  * Ist dies der Fall, muss geprüft werden, ob diese Substanzen unterschiedliche Formeln haben.
	  * Ist dies der Fall, soll abgefragt werden, welcher Substanz die vereinende URN zugewiesen werden soll.
	  * 
	  * 
	  */
		
		try {
			execute("INSERT INTO substances VALUES ("+id+", "+dbString(newFormula)+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod(id);
		return id;
	}
	
	private static Integer askAndAssignUrn(URL sourceOfNewEntry, URN urnLinkedFromNewEntry, int idOfNewEntry, Formula newFormula, int idOfExistingSubstance) throws SQLException, IOException, NoTokenException, DataFormatException {
		Tools.startMethod("askAndAssignUrn("+urnLinkedFromNewEntry+", newId: "+idOfNewEntry+", source: "+sourceOfNewEntry+", present id: "+idOfExistingSubstance+")");
		Collection<URL> oldSourceURLs=getReferencingURLs(urnLinkedFromNewEntry);
		
		/* Initialize */
		String databaseKey = sourceOfNewEntry+" <"+urnLinkedFromNewEntry+"> "+oldSourceURLs;		
		Integer decision=null; 
		
		/* get urn suffix */
		String suffixOfUrnLinkedFromNewEntry=urnLinkedFromNewEntry.suffix();
		
		TreeSet<Formula> formulasAssignedToUrn = getFormulasFromURNResolutionPages(urnLinkedFromNewEntry);
		
		/* try to assign urn to one of the urls: 
		 * If one of the URLs ends reflects the URN directly, then the urn should be assigned to this */
		if (sourceOfNewEntry.toString().endsWith(suffixOfUrnLinkedFromNewEntry)) {
			decision=ASSIGN_TO_NEW;
		}
		if (decision==null) {			
			for (URL url : oldSourceURLs) {
				if (url.toString().endsWith(suffixOfUrnLinkedFromNewEntry)) {
					decision=ASSIGN_TO_OLD;
					break;
				}			
			}
		}
		if (decision==null && formulasAssignedToUrn!=null){
			Formula formulaOfExistingEntry=getFormula(idOfExistingSubstance);
			for (Formula formulaAssignedToUrn:formulasAssignedToUrn){
				if (formulaAssignedToUrn.equals(newFormula)) {
					decision=ASSIGN_TO_NEW;
					break;
				}
				if (formulaAssignedToUrn.equals(formulaOfExistingEntry)){
					decision=ASSIGN_TO_OLD;
					break;
				}
			}
		}
		
		/* if automatic assignment available: write to database */
		if (decision!=null) addDecision(databaseKey,decision,true);
		
		/* if not assigned: try to load from decision database */
		if (decision==null) decision=getDecision(databaseKey);
		
		/* if still not assigned (i.e. not in decision database: ask user */
		if (decision==null){
			TreeSet<URL> urls = Tools.URLSet();
			urls.addAll(oldSourceURLs);
			urls.addAll(urnLinkedFromNewEntry.urls());
			urls.add(sourceOfNewEntry);
			for (URL url : urls){
				try {
					Runtime.getRuntime().exec("gnome-open "+url);
					Thread.sleep(1000);
				} catch (IOException e) {
				} catch (InterruptedException e) {  }
			}
			decision = JOptionPane.showOptionDialog(null, "To which substance shall the urn ("+urnLinkedFromNewEntry+") be assigned?", "Feedback",JOptionPane.YES_NO_CANCEL_OPTION,  JOptionPane.INFORMATION_MESSAGE, null, new String[]{""+sourceOfNewEntry, ("<html>"+oldSourceURLs).replace("[", "").replace("]", "").replace(", ", "<br>"),"None of them!"},  "default");
			if (decision==2){
				decision=DEASSIGN;
			}
			
			/* store user dcision */
			addDecision(databaseKey, decision, false);

		}
		if (decision!=null){
			switch (decision) {
			case DEASSIGN:
				execute("UPDATE urns SET id=NULL WHERE urn="+dbString(urnLinkedFromNewEntry)); // de-assign urn from substance
				break;
			case ASSIGN_TO_NEW:
				execute("UPDATE urns SET id="+idOfNewEntry+" WHERE urn="+dbString(urnLinkedFromNewEntry)); // re-assign urn to substance
				break;
			case ASSIGN_TO_OLD:	// keep the urn be assigned to the existing id
				break;
			default:
				decision=askAndAssignUrn(sourceOfNewEntry, urnLinkedFromNewEntry, idOfNewEntry, newFormula, idOfExistingSubstance);
				break;
			}
		}
		Tools.endMethod();
		return decision;
  }
	
	public static void addDecision(String databaseKey, Integer decision, boolean automatic) throws SQLException, IOException {
		String query="INSERT INTO decisions VALUES ("+dbString(databaseKey)+", "+decision+", "+(automatic?"TRUE":"FALSE")+")";		
		try {
			execute(query);
		} catch (SQLException se){
			if (!se.getMessage().startsWith("Duplicate key")){
				System.err.println(query);
				throw se;
			}
		}
  }

	public static Integer getDecision(Object databaseKey) throws SQLException, IOException {
		Integer decision=null;
		Statement st=createStatement();
		ResultSet rs=st.executeQuery("SELECT value FROM decisions WHERE keyphrase="+dbString(databaseKey));
		if (rs.next()) {
			decision=rs.getInt(1);
			System.err.println("Hooray! We used a decision from the local database!");
			try {
		    Thread.sleep(20000);
	    } catch (InterruptedException e) {}
		}
		rs.close();
		st.close();
		return decision;
  }

	public static TreeSet<Formula> getFormulasFromURNResolutionPages(URN urnLinkedFromNewEntry) throws IOException, NoTokenException, DataFormatException, SQLException {
		Tools.startMethod("getFormulasFromURNResolutionPages("+urnLinkedFromNewEntry+")");
		TreeSet<Formula> result=new TreeSet<Formula>(ObjectComparator.get());
		Set<URL> urls = urnLinkedFromNewEntry.urls();
		if (urls==null) {
			Tools.endMethod();
			return null;
		}
		urls=replaceKeggUrls(urls);
		for (URL url: urls){
			Formula  f=getFormulaFrom(url);
			if (f!=null) result.add(f);
		}
		result=result.isEmpty()?null:result;
		Tools.endMethod(result);
	  return result;
  }

	public static Set<URL> replaceKeggUrls(Set<URL> urls) throws MalformedURLException {
		TreeSet<URL> badUrls=Tools.URLSet();
		for (URL url: urls){
			if (url.toString().startsWith("http://www.genome.jp/dbget-bin/www_bget?")) {
				badUrls.add(url);
			}
		}
		for (URL bad:badUrls){
			urls.remove(bad);
			String urlString=bad.toString();
			int index=urlString.length();
			while (--index>0){
				if (Character.isUpperCase(urlString.charAt(index))) break;
			}
			urls.add(new URL("http://rest.kegg.jp/get/"+urlString.substring(index)));
		}
		return urls;
	}

	public static Integer createSubstance(String name, Object formula, TreeSet<URN> urns, URL source) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("createSubstance("+name+", "+formula+", "+urns+", "+source+")");
		int id = createBaseComponent(InteractionDB.SUBSTANCE,source,urns,name);
				
		try {
			execute("INSERT INTO substances VALUES ("+id+", "+dbString(formula)+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod(id);
		return id;
	}
	
	public static int createEnzyme(Collection<String> names, String ec, Integer sid, URN urn, URL source) throws SQLException, IOException{
		Tools.startMethod("createEnzyme("+names+", "+ec+", "+sid+", "+urn+", "+source+")");
		int id=createBaseComponent(InteractionDB.ENZYME,source,urn,names);		
		try {
			execute("INSERT INTO enzymes VALUES ("+id+","+dbString(ec)+","+((sid==null)?"NULL":sid)+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod(id);
		return id;
	}

	public static int createEnzyme(Collection<String> names, String ec, Integer sid, Collection<URN> urns, URL source) throws SQLException, NoSuchMethodException, IOException{
		Tools.startMethod("createEnzyme("+names+", "+ec+", "+sid+", "+urns+", "+source+")");
		int id=createBaseComponent(InteractionDB.ENZYME,source,urns,names);		
		try {
			execute("INSERT INTO enzymes VALUES ("+id+","+dbString(ec)+","+((sid==null)?"NULL":sid)+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod(id);
		Tools.indent("");
		return id;
	}
	
	public static int createCompartment(String name, URN urn, int group, URL source) throws SQLException, IOException {
		Tools.startMethod("createCompartment("+name+", "+urn+", "+group+", "+source+")");
		int cid=createBaseComponent(COMPARTMENT, source, urn, name);
		execute("INSERT INTO compartments VALUES ("+cid+", "+group+")");
	  Tools.endMethod(cid);
		return cid;
  }
	
	public static Integer createCompartment(String name, TreeSet<URN> urns, int group, URL source) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("createCompartment("+name+", "+urns+", "+group+", "+source+")");
		int cid=createBaseComponent(COMPARTMENT, source, urns, name);
		try {
			execute("INSERT INTO compartments VALUES ("+cid+", "+group+")");
		} catch (SQLException e) {
			if (!e.getMessage().contains("Duplicate key")) throw e; 
		}
	  Tools.endMethod(cid);
		return cid;
  }
	
	public static int createPathway(URN urn, String name, URL source) throws SQLException, IOException{
		Tools.startMethod("createPathway("+urn+")");
		int result=createBaseComponent(PATHWAY, source, urn, name);
		Tools.endMethod(result);
		return result;
	}
	
	public static void setSpontan(int rid, boolean spontan) throws SQLException, IOException{
		Tools.startMethod("setSpontan(rid="+rid+", "+spontan+")");
		String query = "SELECT spontan FROM reactions WHERE id=" + rid;
		Statement st=createStatement();
		ResultSet rs = st.executeQuery(query);
		if (rs.next()) {
			if (rs.getBoolean(1)) { // already marked as spontaneous
				rs.close();
			} else {
				rs.close();
				st.close();
				execute("UPDATE reactions SET spontan=" + spontan + " WHERE id=" + rid);
			}
		} else {
			execute("INSERT INTO reactions VALUES (" + rid + ", " + spontan + ")");;
		}
		Tools.endMethod();
	}
	
	public static int createReaction(TreeSet<String> names, TreeSet<URN> urns, boolean spontan, URL source) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("createReaction("+names+", "+urns+", spontan="+spontan+", "+source+")");
		int rid=createBaseComponent(REACTION, source, urns, names);
		setSpontan(rid, spontan);
		Tools.endMethod(rid);
		return rid;
  }
	
	public static int createReaction(String name, TreeSet<URN> urns, boolean spontan, URL source) throws SQLException, NoSuchMethodException, IOException {
		Tools.startMethod("createReaction('"+name+"', "+urns+", spontan="+spontan+", "+source+")");
		int rid=createBaseComponent(REACTION, source, urns, name);
		setSpontan(rid, spontan);
		Tools.endMethod(rid);
		return rid;
  }
	
	public static void addSubstrateToReaction(int rid, int sid, int stoich) throws SQLException, IOException {
		Tools.startMethod("addSubstrateToReaction(rid="+rid+": "+stoich+"×"+sid+")");
		try {
			execute("INSERT INTO substrates VALUES ("+sid+", "+rid+", "+stoich+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod();	  
  }

	public static void addProductToReaction(int rid, int sid, int stoich) throws SQLException, IOException {
		Tools.startMethod("addProductToReaction(rid="+rid+": "+stoich+"×"+sid+")");
		try{
			execute("INSERT INTO products VALUES ("+sid+", "+rid+", "+stoich+")");
		} catch (SQLException e){
			if (!e.getMessage().contains("Duplicate key")) throw e;
		}
		Tools.endMethod();	  
  }
	
	private static TreeSet<Integer> readEnzymeIds(TreeSet<String> ecNumbers) throws SQLException, IOException {
		Tools.startMethod("readEnzymeIds("+ecNumbers+")");
		String query = "SELECT id FROM enzymes WHERE ec IN " + ecNumbers.toString().replace("[", "(\"").replace("]", "\")").replace(",", "\",\"");
		try {
			Statement st=createStatement();
			ResultSet rs=st.executeQuery(query);
			TreeSet<Integer> eids=new TreeSet<Integer>();
			while (rs.next()) eids.add(rs.getInt(1));
			rs.close();
			st.close();
			Tools.endMethod(eids);
			return eids;
		} catch (SQLException e){
			System.err.println(query);
			throw e;
		}
  }
	
	public static int getOrCreateGroup(String category) throws SQLException, IOException {
		Tools.startMethod("getOrCreateGroup("+category+")");
		// TODO: replace by called method?
		int result = getOrCreateNid(category);
		Tools.endMethod(result);
		return result; 		
  }
	
	public static Formula getFormula(int id) throws SQLException, DataFormatException, IOException {
		Tools.startMethod("getFormula("+id+")");
		String query = "SELECT formula FROM substances WHERE id=" + id;
		Tools.indent(query);
		try {
			Statement s = createStatement();
			ResultSet r = s.executeQuery(query);
			Formula result=null;
			if (r.next()) {
				String dummy=r.getString(1);
				if (dummy!=null) result = new Formula(dummy);
			}
			Tools.endMethod(result);
			return result;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}
	
	public static TreeMap<Integer, Integer> loadProducts(int id) throws SQLException, IOException {
		Tools.startMethod("loadProducts("+id+")");
		String query = "SELECT sid,stoich FROM products WHERE rid=" + id;
		try {
			Statement st = InteractionDB.createStatement();
			ResultSet rs = st.executeQuery(query);
			TreeMap<Integer, Integer> products = new TreeMap<Integer, Integer>();
			while (rs.next())	products.put(rs.getInt(1), rs.getInt(2));
			rs.close();
			st.close();
			Tools.endMethod(products);
			return products;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}

	public static TreeMap<Integer, Integer> loadSubstrates(int id) throws SQLException, IOException {		
		Tools.startMethod("loadSubstrates("+id+")");
		String query = "SELECT sid,stoich FROM substrates WHERE rid=" + id;
		try {
			TreeMap<Integer, Integer> set = new TreeMap<Integer, Integer>();
			Statement st = InteractionDB.createStatement();
			ResultSet rs = st.executeQuery(query);
			while (rs.next())
				set.put(rs.getInt(1), rs.getInt(2));
			rs.close();
			st.close();
			Tools.endMethod(set);
			return set;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}
	
	public static byte readDirections(int cid, int rid) throws SQLException, IOException {
		Tools.startMethod("readDirections(cid: "+cid+", rid: "+rid+")");
		String query = "SELECT forward,backward FROM reaction_directions WHERE cid=" + cid + " AND rid=" + rid;
		try {
			Statement st = createStatement();
			ResultSet rs = st.executeQuery(query);
			byte dir = 0;
			if (rs.next()) {
				if (rs.getBoolean(1)) dir += Reaction.FORWARD; // if forward flag set: save "+1" (forward)
				if (rs.getBoolean(2)) dir += Reaction.BACKWARD; // if backward flag set: save "-1" (backward)
			}
			rs.close();
			st.close();
			Tools.endMethod(dir);
			return dir;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}
	
	public static TreeSet<Integer> loadEnzymesOfCompartment(int cid) throws SQLException, IOException {
		Tools.startMethod("loadEnzymesOfCompartment("+cid+")");
		String query = "SELECT eid FROM enzymes_compartments WHERE cid="+cid;
		try {
			Statement st = InteractionDB.createStatement();
			TreeSet<Integer> enzymes = new TreeSet<Integer>();
			ResultSet rs = st.executeQuery(query);
			while (rs.next())
				enzymes.add(rs.getInt(1));
			rs.close();
			st.close();
			Tools.endMethod(enzymes);
			return enzymes;
		} catch (SQLException e) {
			System.err.println(query);
			throw e;
		}
	}
	
	public static TreeSet<Integer> getSpontaneousReactionsActingOn(TreeSet<Integer> sids) throws SQLException, IOException {
		Tools.startMethod("getSpontaneousReactionsActingOn("+sids+")");
		String query = null;
		try {
			Statement st = createStatement();
			TreeSet<Integer> reactions = new TreeSet<Integer>();
			if (sids.isEmpty()) {
				Tools.endMethod(reactions);
				return reactions;
			}
			query = "SELECT rid FROM substrates WHERE sid IN " + sids.toString().replace("[", "(").replace("]", ")") + " AND rid IN (SELECT id FROM reactions WHERE spontan)";
			// System.out.println(query);
			ResultSet rs = st.executeQuery(query);
			while (rs.next())
				reactions.add(rs.getInt(1));
			query = "SELECT rid FROM products WHERE sid IN " + sids.toString().replace("[", "(").replace("]", ")") + " AND rid IN (SELECT id FROM reactions WHERE spontan)";
			// System.out.println(query);
			rs = st.executeQuery(query);
			while (rs.next())
				reactions.add(rs.getInt(1));
			rs.close();
			st.close();
			Tools.endMethod(reactions);
			return reactions;
		} catch (SQLException e) {
			System.err.println("Error on " + query);
			throw e;
		}
	}
	
//******** organism components ***********************************
	
/* 
	 * @throws MalformedURLException 
	 * @throws DataFormatException *************/

	public static TreeSet<Integer> getCompartmentGroupIds() throws IOException {
		Tools.startMethod("getCompartmentGroupIds()");
		String query="SELECT DISTINCT groups FROM compartments";
		TreeSet<Integer> result = new TreeSet<Integer>();
		try {
			Statement st=createStatement();
			ResultSet rs=st.executeQuery(query);
			while (rs.next())	result.add(rs.getInt(1));
		} catch (SQLException e){
			System.err.println(query);
		}
		Tools.endMethod(result);
		return result;
  }

	/**
	 * reads the ids of those substances, which have multiple urls assigned
	 * @return vector of ids
	 * @throws SQLException
	 * @throws IOException 
	 */
	public static Vector<Integer> getIdsOfSubstancesWithMultipleReferencingURLs() throws SQLException, IOException {
		Tools.startMethod("getIdsOfSubstancesWithMultipleReferencingURLs()");
		String query="SELECT id FROM ids NATURAL JOIN urns NATURAL JOIN urn_urls WHERE type="+SUBSTANCE+" GROUP BY id HAVING COUNT(DISTINCT lid)>1";
		try {
			Statement st=createStatement();
	    ResultSet rs=st.executeQuery(query);
	    Vector<Integer> result=new Vector<Integer>();
	    while (rs.next()) result.add(rs.getInt(1));
	    rs.close();
	    st.close();
	    Tools.endMethod(result);
		  return result;
    } catch (SQLException e) {
    	System.err.println(query);
	    throw e;
    }
  }

	public static void setDateMark(String string) throws SQLException, IOException {
		Tools.startMethod("setDateMark("+string+")");
		SimpleDateFormat df = new SimpleDateFormat("yyyy-MM-dd");
		String date=df.format(new Date());
		String query="INSERT INTO dates VALUES (0,'"+date+"' ,"+dbString(string)+")";
		execute(query);
		Tools.endMethod();
  }

	public static Formula getGlycanFormula(String key) throws DataFormatException, SQLException, IOException {
		Tools.startMethod("getGlycanFormula("+key+")");
		String query="SELECT id FROM abbrevations WHERE abbr="+dbString(key);
		Statement st = createStatement();
		ResultSet rs=st.executeQuery(query);
		Formula result=null;
		if (rs.next()){
			int id=rs.getInt(1);
			result=getFormula(id);
		}
		if (result==null) Tools.warn("Can not resolve "+key);
		Tools.endMethod(result);
		return result;
  }


	public static void createAbbrevation(String code, String keggId) throws DataFormatException, SQLException, IOException {
		if (!keggId.startsWith("C")) throw new DataFormatException("Expected Kegg Compound id, found "+keggId+" instead.");
 		int aid=getOrCreateIdFor(new KeggCompoundUrn(keggId), SUBSTANCE);
		String query="INSERT INTO abbrevations VALUES ("+dbString(code)+", "+aid+")";
		System.out.println(query);
		execute(query);
  }
	
	public static Formula deriveFormulaFromKCF(URL url) throws IOException, DataFormatException, SQLException {
		Tools.startMethod("deriveFormulaFromKCF("+url+")");
		String data = PageFetcher.fetch(url).toString();
		if (!data.contains("NODE")) return null;
		
		String [] lines = data.split("\n");
		int lineCount=lines.length;
		Formula sum=null;
		boolean missingAbbrevation=false;
		
		int lineNumber=0;
		while (lineNumber<lineCount && !lines[lineNumber].startsWith("NODE")) lineNumber++;
		lineNumber++; // the line holding the "NODE" keyword only gives the number of nodes

		while (lineNumber<lineCount && !lines[lineNumber].startsWith("EDGE"))	{
			Formula formula=null;
			
			String line=lines[lineNumber].substring(16);
			int end=line.indexOf(' ');			
			String abbrevation=line.substring(0,end);
			if (!unresolvedAbbrevations.contains(abbrevation)) formula=getGlycanFormula(abbrevation);
			if (formula==null){
				missingAbbrevation=true;
				unresolvedAbbrevations.add(abbrevation);
			} else if (sum==null) {
				sum=formula;
			} else sum.add(formula);
			lineNumber++;			
		}
		if (missingAbbrevation){
			if (Tools.warnOnce("missing resolution for: "+unresolvedAbbrevations)) {
			/*	try {
					Thread.sleep(5000);
				} catch (InterruptedException e){} */
			}
			Tools.endMethod(null);
			return null;
		}
		if (lines[lineNumber].startsWith("EDGE")){
			int bonds=Integer.parseInt(lines[lineNumber].substring(6).trim());
			if (bonds>0){
				Formula water=new Formula("H2O");
				sum.subtract(water.multiply(bonds)); // for every bond formed, one molecule of water is released
			}
		}
		Tools.endMethod(sum);
	  return sum;
  }
	
	public static Formula getFormulaFrom(URL url) throws IOException, NoTokenException, DataFormatException, SQLException {
		Tools.startMethod("getFormulaFrom("+url+")");
		String formulaCode=null;		
		if (formulaMap.containsKey(url)){
		  Formula formula=formulaMap.get(url);
			Tools.endMethod(formula);
			Tools.disableLogging();
		  return formula;
		}
		if (url.toString().contains("http://rest.kegg.jp/get")) {
			formulaCode=getFormulaCodeFromKeggApi(url);
		} else if (url.toString().contains("genome.jp/dbget-bin/www_bget?")) {
			formulaCode=getFormulaCodeFromKegg(url);
			throw new UnexpectedException("InteractionDB.getFormula called with "+url);
		} else if (url.toString().contains("lipidmaps.org/data/get_lm_lipids_dbgif.php")){
			formulaCode=getFormulaCodeFromLipidMaps(url);
		} else if (url.toString().contains("drugbank.ca/drugs")){
			formulaCode=getFormulaCodeFromDrugBank(url);
		} else if (url.toString().contains("kanaya.naist.jp/knapsack_jsp/information.jsp")){
			formulaCode=getFormulaCodeFromKnapsack(url);
		} else if (url.toString().contains("ebi.ac.uk/chebi/searchId.do")){
			formulaCode=getFormulaCodeFromChebi(url);
		} else if (url.toString().contains("ebi.ac.uk/ontology-lookup")){
			formulaCode=getFormulaCodeFromEbi(url);
		} else if (url.toString().contains("nikkajiweb.jst.go.jp/nikkaji_web/pages/top_e.jsp")){
			formulaCode=getFormulaCodeFromJCSD(url);
		} else if (url.toString().contains("lipidbank.jp/cgi-bin/detail.cgi")){
			formulaCode=getFormulaCodeFromLipidBank(url);
		} else if (url.toString().contains("3dmet.dna.affrc.go.jp/cgi/show_data.php")){
			formulaCode=getFormulaCodeFrom3DMet(url);
		} else if (url.toString().contains("ncbi.nlm.nih.gov/sites/entrez?db=pccompound")){
			formulaCode=getFormulaCodeFromPubChemCompound(url);
		} else if (url.toString().contains("pubchem.ncbi.nlm.nih.gov/summary/summary.cgi")){
			formulaCode=getFormulaCodeFromPubChemCompound(url);			
		} else {
			int trialsLeft=2;
			String code=null;
			while (true){
				try {
					code=PageFetcher.fetch(url).toString();
				} catch (IOException e){
					trialsLeft--;
					if (trialsLeft==0) throw e;
				}
				if (code!=null) break;
			}
			code=code.toUpperCase().replace("FORMULATION", "").replace("RELEASE FORMULA", "").replace("MEDIA FLOW FORMULA XL", "").replace("TRYPTEC FORMULA", "").replace("<P> FORMULA [KEGG COMPOUND </P>", "");
			
			if (code.contains("FORMULA")){
				int pos=code.indexOf("FORMULA");
				pos-=20;
				if (pos<0) pos=0;
				throw new UnknownFormatConversionException(url+" contains string FORMULA:\n"+code.substring(pos,pos+50));
			}
			if (code.contains("FORMEL")){
				int pos=code.indexOf("FORMEL");
				pos-=20;
				if (pos<0) pos=0;
				throw new UnknownFormatConversionException(url+" contains string FORMEL:\n"+code.substring(pos,pos+50));
			}
		}
		if (formulaCode!=null && (formulaCode.equals("-") || formulaCode.equals(""))) {
			formulaCode=null;
		} 
		Formula result=null;
		try {
			if (formulaCode!=null) result=new Formula(formulaCode);
		} catch (DataFormatException dfe){
			System.err.println(dfe.getMessage());
			throw new DataFormatException("@ "+url);
		}
		formulaMap.put(url, result);
		Tools.endMethod(result);
	  return result;
  }
	
	private static String getFormulaCodeFromEbi(URL url) throws IOException {
		Tools.startMethod("getFormulaCodeFromEbi("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			String line=lines[i];
			int start=line.indexOf("FORMULA");
			if (start>0){
				start=line.indexOf("<td",start);
				int end=line.indexOf("</tr>", start);
				formula=Tools.removeHtml(line.substring(start,end));
				end=formula.lastIndexOf('[');
				if (end>0) formula=formula.substring(0,end).trim(); 
			}
		}
		Tools.noteOnce(url+" returns formula "+formula);
/*		try {
	    Thread.sleep(30000);
    } catch (InterruptedException e) {} */
		Tools.endMethod(formula);
	  return formula;
  }

	public static String getFormulaCodeFromDrugBank(URL url) throws IOException {
		Tools.startMethod("getFormulaCodeFromDrugBank("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			String line=lines[i];
			if (line.contains("Chemical Formula<")) {				
				formula = removeHtml(lines[++i]);
				if (formula==null || formula.length()==0){
					formula=null;
				} else break;
			} else 
				// workarounds:
			if (line.contains("Formula<") && !line.contains("Chemical Formula") && (!line.contains("Allergy Formula")) && (!line.contains("Cough Formula"))&& (!line.contains("Triaminic AM Decongestant Formula"))&& (!line.contains("Children Formula")) && (!line.contains("C.H.V. Formula"))&& (!line.contains("C.V. Formula"))){
				System.out.println("found the following code snippet in "+url+" :");
				System.out.println(lines[i-2]);
				System.out.println(lines[i-1]);
				System.out.println(lines[i]);
				System.out.println(lines[i+1]);
				System.out.println(lines[i+2]);
				System.exit(0);				
			}
		}
		Tools.endMethod(formula);
	  return formula;
  }

	private static String getFormulaCodeFromPubChemCompound(URL url) throws IOException {
		Tools.startMethod("getFormulaCodeFromPubChemCompound("+url+")");		
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			String line=lines[i];
			int index=line.indexOf("Formula:<");
			if (index>0){
				index=line.indexOf(">",index)+1;
				int end=line.indexOf("&nbsp;",index);
				formula=removeHtml(line.substring(index,end));
				break;
			}
			index=line.indexOf("MF:");
			if (index>0){
				index=line.indexOf(">",index)+1;
				int end=line.indexOf("</dd>",index);
				formula=removeHtml(line.substring(index,end));
				break;
			}
		}		
		Tools.endMethod(formula);
	  return formula;
  }

	private static String getFormulaCodeFromKnapsack(URL url) throws IOException {
		Tools.startMethod("getFormulaCodeFromKnapsack("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">Formula<")) {
				formula = removeHtml(lines[++i]);
				break;
			}
		}
		Tools.endMethod(formula);
	  return formula;
  }

	private static String getFormulaCodeFrom3DMet(URL url) throws IOException {
		Tools.startMethod("getFormulaCodeFrom3DMet("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">Formula<")) {
				formula = removeHtml(lines[++i]);
				break;
			}
		}
		Tools.endMethod(formula);
	  return formula;
  }

	private static String getFormulaCodeFromLipidBank(URL url) throws IOException, DataFormatException {
		Tools.startMethod("getFormulaCodeFromLipidBank("+url+")");
		String[]lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">FORMULA<")){
				formula=removeHtml(lines[i]);
				int idx=formula.indexOf("MOL.WT");
				if (idx>0) formula=formula.substring(0,idx);
				formula=formula.replace("FORMULA:", "").trim();
				if (formula.length()==0) formula=null;
			}
		}
		Tools.endMethod(formula);
		return formula;
  }

	private static String getFormulaCodeFromJCSD(URL url) throws IOException, NoTokenException, DataFormatException {
		Tools.startMethod("getFormulaCodeFromJCSD("+url+")");
		String[]lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">MF</span>")){
				while (!lines[++i].contains("span")){
					if (i>lines.length) throw new DataFormatException("Formula tag found in "+url+", but no formula reckognized!");
				}
				formula=removeHtml(lines[i]);
			}
		}
		Tools.endMethod(formula);
		return formula;
  }

	private static String getFormulaCodeFromChebi(URL url) throws IOException, DataFormatException {
		Tools.startMethod("getFormulaCodeFromChebi("+url+")");
		String[]lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">Form")){
				while (!lines[i].contains("Content")){
					i++;
					if (i>lines.length) throw new DataFormatException("Formula tag found in "+url+", but no formula reckognized!");
				}
				formula=lines[++i].trim();
			}
		}
		Tools.endMethod(formula);
		return formula;
  }

	private static String getFormulaCodeFromLipidMaps(URL url) throws IOException, NoTokenException {
		Tools.startMethod("getFormulaCodeFromLipidMaps("+url+")");
		String[]lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains(">Formula<")){
				formula=removeHtml(lines[i].replace("Formula", ""));
			}
		}
		Tools.endMethod(formula);
		return formula;
  }
	
	private static String getFormulaCodeFromKeggApi(URL url) throws IOException, DataFormatException, SQLException {
		Tools.startMethod("getFormulaCodeFromKegg("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (String line:lines){
			if (line.startsWith("FORMULA")) {
				formula = line.substring(12).trim();
				break;
			}
		}
		if (formula==null && url.toString().contains("http://rest.kegg.jp/get/G")) {
			Formula dummy = deriveFormulaFromKCF(url);			
			formula=dummy==null?null:dummy.toString();
		}

		Tools.endMethod(formula);
	  return formula;
  }

	private static String getFormulaCodeFromKegg(URL url) throws IOException, DataFormatException, SQLException {
		Tools.startMethod("getFormulaCodeFromKegg("+url+")");
		String[] lines=PageFetcher.fetchLines(url);
		String formula=null;
		for (int i=0; i<lines.length; i++){
			if (lines[i].contains("<nobr>Formula</nobr>")) {
				formula = removeHtml(lines[++i]);
				break;
			}
		}
		if (formula==null && url.toString().contains("genome.jp/dbget-bin/www_bget?G")) {
			Formula dummy = deriveFormulaFromKCF(new URL(url.toString().replace("www_bget?G", "www_bget?-f+k+glycan+G")));			
			formula=dummy==null?null:dummy.toString();
			throw new UnexpectedException("InteractionDB.getFormulaCodeFromKegg called with "+url);

		}

		Tools.endMethod(formula);
	  return formula;
  }

	private static String removeHtml(String string) {		
	  return Tools.removeHtml(string.replace("<sup>", "^")).trim();
  }

	public static void preprareAbbrevations(TreeMap<String, Integer> mappingFromKeggSubstanceIdsToDbIds, boolean skipKeggLinks) throws NameNotFoundException, SQLException, IOException, NoSuchMethodException, DataFormatException, AlreadyBoundException, NoTokenException {
		Tools.startMethod("preprareAbbrevations("+mappingFromKeggSubstanceIdsToDbIds+")");
		Stack<String> referencedSubstanceIds = readMonosaccarideCodes();
		
		addAbbrevation("ADP","C00008",referencedSubstanceIds);
		addAbbrevation("Ala","C00041",referencedSubstanceIds);
		addAbbrevation("Arg","C00062",referencedSubstanceIds);
		addAbbrevation("Asn","C00152",referencedSubstanceIds);
		addAbbrevation("Asp","C00049",referencedSubstanceIds);
		addAbbrevation("Cys","C00097",referencedSubstanceIds);
		addAbbrevation("Cer","C00195",referencedSubstanceIds);			
		addAbbrevation("CMP",				"C00055",referencedSubstanceIds);			
		addAbbrevation("Dol","C00381",referencedSubstanceIds);
		addAbbrevation("EtN","C00189",referencedSubstanceIds);
		addAbbrevation("Gln","C00064",referencedSubstanceIds);
		addAbbrevation("GDP","C00035",referencedSubstanceIds);
		addAbbrevation("Glu","C00025",referencedSubstanceIds);
		addAbbrevation("Gly","C00037",referencedSubstanceIds);
		addAbbrevation("Gro","C00116",referencedSubstanceIds);
		addAbbrevation("His","C00135",referencedSubstanceIds);
		addAbbrevation("Ile","C00407",referencedSubstanceIds);
		addAbbrevation("Ino","C00137",referencedSubstanceIds);
		addAbbrevation("Leu","C00123",referencedSubstanceIds);
		addAbbrevation("Lys","C00047",referencedSubstanceIds);
		addAbbrevation("Met","C00073",referencedSubstanceIds);
		addAbbrevation("Neu5Ac",		"C00270",referencedSubstanceIds);
		addAbbrevation("NeuNGc",		"C03410",referencedSubstanceIds);
		addAbbrevation("Oleandrose","C08237",referencedSubstanceIds);
		addAbbrevation("P",  "C00009",referencedSubstanceIds);
		addAbbrevation("Phe","C00079",referencedSubstanceIds);
		addAbbrevation("Pro","C00148",referencedSubstanceIds);
		addAbbrevation("Protein",		"C00017",referencedSubstanceIds);
		addAbbrevation("S",  "C00059",referencedSubstanceIds);
		addAbbrevation("Sec","C05688",referencedSubstanceIds);
		addAbbrevation("Ser","C00065",referencedSubstanceIds);
		addAbbrevation("Thr","C00188",referencedSubstanceIds);
		addAbbrevation("Trp","C00078",referencedSubstanceIds);
		addAbbrevation("Tyr","C00082",referencedSubstanceIds);		
		addAbbrevation("UDP","C00015",referencedSubstanceIds);		
		addAbbrevation("Val","C00183",referencedSubstanceIds);
		while (!referencedSubstanceIds.isEmpty())	parseSubstanceInfo(referencedSubstanceIds, mappingFromKeggSubstanceIdsToDbIds,skipKeggLinks);
		Tools.endMethod(); 
  }
	
	private static Stack<String> readMonosaccarideCodes() throws IOException, DataFormatException, SQLException {
		Tools.startMethod("readMonosaccarideCodes");
		Stack<String> keggSubstanceIds=new Stack<String>();
		String[] lines=PageFetcher.fetchLines("http://www.genome.jp/kegg/catalog/codes2.html");
		for (String line:lines){
			String code=null;
			String keggId=null;
				line=line.trim();
			if (line.startsWith("<tr><td>")){				
				String [] parts=line.split("</td><td>");
				for (String part:parts){
					if (part.contains("href")){
						part=part.substring(part.indexOf('+')+1);
						keggId=part.substring(0,part.indexOf('"'));
						keggSubstanceIds.push(keggId);
					} else if (part.startsWith("<tr>")) {
						code=Tools.removeHtml(part);
					} else part=null;
				}
				if (keggId!=null) InteractionDB.createAbbrevation(code,keggId);
			}
		}
		InteractionDB.setDateMark("Read KEGG monosaccaride codes");
		Tools.endMethod(keggSubstanceIds);
		return keggSubstanceIds;
  }
	
	public static void main(String[] args) throws DataFormatException, SQLException, IOException {	  
	  Statement st=createStatement();
	  ResultSet rs=st.executeQuery("SHOW TABLES");
	  while (rs.next()){
	  	System.out.println(rs.getString(1));
	  }
  }
	
	private static void addAbbrevation(String code, String keggId, Stack<String> referencedSubstanceIds) throws DataFormatException, SQLException, IOException {
		Tools.startMethod("addAbbrevation("+code+", "+keggId+", "+referencedSubstanceIds+")");
	  createAbbrevation(code, keggId);
	  referencedSubstanceIds.push(keggId);	  
	  Tools.endMethod();
  }

	/**
  	 * parse the content of a token describing one kegg substance
  	 * 
  	 * @param unexploredKeggIds the kegg-internal id of the substance, whose data shall be fetched
  	 * @param mappingFromKeggSubstanceIdsToDbIds collects a mapping from the kegg substance ids to their respective ids in the local database
	 * @param skipKeggLinks 
  	 * @param unresolvedAbbrevations 
  	 * @param source 
  	 * @throws SQLException
  	 * @throws IOException
  	 * @throws NameNotFoundException if no name is found within the substance description file
  	 * @throws NoSuchMethodException
  	 * @throws DataFormatException
  	 * @throws AlreadyBoundException 
  	 * @throws NoTokenException 
  	 */
	
	 	public static boolean parseSubstanceInfo(Stack<String> unexploredKeggIds, TreeMap<String, Integer> mappingFromKeggSubstanceIdsToDbIds, boolean skipKeggLinks) throws SQLException, IOException, NameNotFoundException, NoSuchMethodException, DataFormatException, AlreadyBoundException, NoTokenException {
  		Tools.startMethod("parseSubstanceInfo(...,...)");
  		String keggSubstanceId = unexploredKeggIds.pop();
  		
  		if (mappingFromKeggSubstanceIdsToDbIds.containsKey(keggSubstanceId)) {
  			Tools.indent(keggSubstanceId + " already analyzed");
  			Tools.endMethod(false);
  			return false;
  		}
  		KeggUrn substanceUrn = urnForComponent(keggSubstanceId);
  		
  		Tools.indent("parsing "+keggSubstanceId);
  		if (!Tools.logging()) System.out.println("parsing " + substanceUrn + "...");
  		
  		if (substanceUrn == null) {
  			Tools.endMethod();
  			throw new DataFormatException("Can not create URN for "+keggSubstanceId);
  		}
  
  		TreeSet<String> names = Tools.StringSet();
  
  		TreeSet<URN> urns = new TreeSet<URN>(ObjectComparator.get());
  		urns.add(substanceUrn);
  
  		String data = substanceUrn.fetch();
  
  		if (data.length() < 5) {
  			Tools.endMethod(false);
  			return false;
  		}
  
  		/************ the following lines of code are fixes for some special entries *******************************/
  
/*  		if (data.contains("No such database")) {
  			if (keggSubstanceId.startsWith("C06125LECTIN") || keggSubstanceId.startsWith("C04927LECTIN") || keggSubstanceId.startsWith("C04911LECTIN") || keggSubstanceId.startsWith("C03405LECTIN") || keggSubstanceId.startsWith("C02352LECTIN")) {
  				Tools.endMethod();
  				return false; // has some remarks, that are hard to parse, but are also not of interest
  			} else throw new IllegalArgumentException("was not able to create valid url from content of " + keggSubstanceId);
  		}*/

  		String lowerDescription=data.toLowerCase();
  		int pos=lowerDescription.indexOf("obsolete");
  		if (pos>0 && pos!=lowerDescription.indexOf("obsolete pesticide")){
  			Runtime.getRuntime().exec("gnome-open "+substanceUrn.url());
  			throw new IllegalArgumentException("found \"obsolete\" keyword in file! going to sleep");
  		}
  
  		/************** end of fixes *****************************/
  
  		String[] lines = data.split("\n");
  		Formula formula = null;
  		TreeSet<String> synonyms = Tools.StringSet();
  		String definition=null;
  		for (int i = 0; i < lines.length; i++) {
  			String line=lines[i];
  			if (line.startsWith("NAME") || line.startsWith("COMPOSITION")) {  				
  				String name=line.substring(12).trim();
  				if (name.endsWith(";")) name=name.substring(0, name.length()-1);
  				if (name.startsWith("[") && name.endsWith("]") && name.indexOf("[", 1)<0) name=name.substring(1,name.length()-1); // resolve [name] to name
  				names.add(name);
  				while (lines[i+1].startsWith(" ")) {
  					name = lines[++i].trim();
  	  				if (name.endsWith(";")) name=name.substring(0, name.length()-1);
  	  				names.add(name);
   				}
  			}
  			if (line.startsWith("DEFINITION")) {
  				definition=line.substring(12).trim();
  			}
  
  			if (line.startsWith("FORMULA")) {
  				String dummy=line.substring(12).trim();
 					if (dummy!=null && dummy.length()>0) {
 						if (keggSubstanceId.equals("D09947")
 								||keggSubstanceId.equals("D02852")
 								||keggSubstanceId.equals("D02856")
 								||keggSubstanceId.equals("D02863")
 								||keggSubstanceId.equals("D06178")
 								||keggSubstanceId.equals("D09912")
 								||keggSubstanceId.equals("D09632")
 								||keggSubstanceId.equals("D00992")
 								||keggSubstanceId.equals("D06502")){
 							Tools.warn("Skipped formula of "+keggSubstanceId+".\nThe last time we visited it, it had a corrupt formula!");
 							// TODO: check http://rest.kegg.jp/get/<keggSubstanceId> for whether the formula has been corrected 							
 						} else
 						try {
 							formula = new Formula(dummy);
 						} catch (Exception e){ // ok something went wrong. Let's do it again, but this time show verbose output
 							Tools.enableLogging();
 							Tools.resetIntendation();
 							formula = new Formula(dummy);
 						}
 					}
  			}
  			
  			if (line.startsWith("DBLINKS") && !skipKeggLinks) {
  				boolean stop=false;
  				line=line.substring(12).trim();
  				while (true) { 					
  					
  					pos = line.indexOf(':');
  					if (pos < 0) Tools.dieLoudly("DB-Reference not structured with ':'");
  					String key = line.substring(0, pos).trim().toUpperCase();
  					String[] values = line.substring(pos + 1).trim().split(" ");
  					for (int v = 0; v < values.length; v++) {
  						String value = values[v];
  						if (key.equals("GLYCOMEDB")) {
  							try {
  								Integer.parseInt(value);
  								URN gdburn = new GlycomeDBurn(value);
  								urns.add(gdburn);
  							} catch (NumberFormatException e) {
  								Tools.warnOnce(value + " is not a Glycome DB code!");
  							}
  						} else if (key.equals("CHEBI")) {
  							try {
  								Integer.parseInt(value);
  								URN chebiurn = new ChEBIUrn(value);
  								urns.add(chebiurn);
  							} catch (NumberFormatException e) {
  								Tools.warnOnce(value + " is not a Glycome DB code!");
  							}
  						} else if (key.equals("PUBCHEM")) {
  							try {
  								Integer.parseInt(value);
  								
  								/* there are two different kinds of pubchen links! */
  								
								URN pcsu = new PubChemSubstanceUrn(value);
								urns.add(pcsu);
  							} catch (NumberFormatException e) {
  								Tools.warnOnce(value + " is not a Glycome DB code!");
  							}
  						} else if (key.equals("JCGGDB")) {
  							// currently ignored
  						} else if (key.equals("CCSD")) {
  							// currently ignored
  						} else if (key.equals("LIGANDBOX")) {
  							// currently ignored
  						} else if (key.equals("PDB-CCD")) {
  							// currently ignored
  						} else if (key.equals("LIPIDBANK")) {
  							URN gdburn = new LipidBankUrn(value);
  							urns.add(gdburn);
  						} else if (key.equals("3DMET")) {
  							URN gdburn = new threeDMetUrn(value);
  							urns.add(gdburn);
  						} else if (key.equals("NIKKAJI")) {
  							URN gdburn = new JcsdUrn(value);
  							urns.add(gdburn);
  						} else if (key.equals("LIPIDMAPS")) {
  							URN gdburn = new LipidMapsUrn(value);
  							urns.add(gdburn);
  						} else if (key.equals("KNAPSACK")) {
  							URN gdburn = new KnapsackUrn(value);
  							urns.add(gdburn);
  						} else if (key.equals("CAS")) {
  							URN gdburn = new CasUrn(value);
  							urns.add(gdburn);
  							//stop=true;
  						} else if (key.equals("DRUGBANK")) {
  							URN gdburn = new DrugBankUrn(value);
  							urns.add(gdburn);
  						} else {
  							throw new DataFormatException("found reference to unknown database: " + key + " => " + value);
  						}
  					}
  					if (!lines[i+1].startsWith(" ")) break;
  					line=lines[++i];
  				}
  				if (stop) {
  					System.out.println(urns);
  					System.exit(0);
  				}
  			}
  
  			if (line.startsWith("REMARK")) {
  				boolean sameAs=false;
  				while (true){
  	  				String remark = line.substring(12).trim();  	  				
				
  	  				if (remark.contains("Same as:")) sameAs=true;
  	  				if (sameAs){
  	  					if (remark.startsWith("ATC code:")) sameAs=false;
  	  					if (remark.startsWith("Therapeutic category:")) sameAs=false;
  	  					if (remark.startsWith("LECTIN:")) sameAs=false;
  	  				}
  	  				
  	  				if (sameAs){  	  					
  						String[] ids = remark.replace("Same as:", "").split(" ");
  						for (String id:ids) {
  							if (id.length() < 6) continue;
  							String keggId = id.substring(0, 6);
  							URN alternativeUrn = urnForComponent(keggId);
  							if (alternativeUrn!=null){
  								synonyms.add(keggId);
  								if (alternativeUrn != null) urns.add(alternativeUrn);
  							} else {  								
  								System.err.println("something's wrong with "+line.trim());
  								System.exit(-1);
  							}
  						}
  	  				}
  	  				
  					if (!lines[i+1].startsWith(" ")) break;
  					line=lines[++i];
  				}
  				
  			}
  		}
  		if (data.contains("No such data")) {
  			names.add("missing substance");
  		} else {
  			if (keggSubstanceId.startsWith("G")){
  				Formula derivedFormula=InteractionDB.deriveFormulaFromKCF(new URL("http://rest.kegg.jp/get/"+keggSubstanceId));
  				if (formula==null){
  					formula=derivedFormula;
  				} else {
  					if (!formula.equals(derivedFormula)) throw new AlreadyBoundException("Derived formula ("+derivedFormula+") differs from previously given formula ("+formula+") of "+keggSubstanceId);
  				}
  			}
  		}
  
  		if (formula==null) Tools.note("no formula!");
  		if (names.isEmpty()) {
  			if (definition != null) {
  				Tools.warn("No name found for "+keggSubstanceId+", using definition: \""+definition+"\".");
  				names.add(definition);
  			} else throw new NameNotFoundException();
  		}
  
  		if (synonyms.size() > 5) {
  			System.err.println("compound with numerous synonyms. check: " + synonyms + " (" + synonyms.size() + ")");
  			System.err.println(urns);
  			if (!(keggSubstanceId.equals("C00089") || keggSubstanceId.equals("C01768") || keggSubstanceId.equals("D02324") || keggSubstanceId.equals("G00370"))) {
  				System.exit(0);
  			}
  		}
  
  		for (Iterator<String> it = synonyms.iterator(); it.hasNext();) unexploredKeggIds.push(it.next());
  		
  		int sid=InteractionDB.createSubstance(names, formula, urns, substanceUrn.url());
  
  //		int sid = InteractionDB.getOrCreateSubstanceId(urns,substanceUrn);
  		mappingFromKeggSubstanceIdsToDbIds.put(keggSubstanceId, sid);
  
  //		InteractionDB.setNames(sid, names);
  //		if (formula != null) InteractionDB.setFormula(sid, formula);
  
  		Tools.endMethod(true);
  		return true;
  	}
  	
  	public static String keggIdFrom(String URLorURN){
  		if (URLorURN.startsWith("http")||URLorURN.startsWith("urn:miriam:kegg")) return URLorURN.substring(URLorURN.length()-6);
			return null;
  	}
  	
  	public static KeggUrn urnForComponent(String keggId) throws MalformedURLException, DataFormatException {
		try {
			Integer.parseInt(keggId.substring(1));
	  		if (keggId.startsWith("C")) return new KeggCompoundUrn(keggId);
	  		if (keggId.startsWith("G")) return new KeggGlycanUrn(keggId);
	  		if (keggId.startsWith("R")) return new KeggReactionUrn(keggId);
	  		if (keggId.startsWith("D")) return new KeggDrugUrn(keggId);
	  		if (keggId.startsWith("E")) return new KeggEDrugUrn(keggId);
		} catch (NumberFormatException e) {}
		System.err.println("\"" + keggId + "\" is not a valid kegg id, skipping.");
  		return null;
  	}
  	
  	public static void printMissingAbbrevations() throws SQLException, IOException{
  		System.out.println("unresolved abbrevations:");
  		Statement st=createStatement();
  		for (String abbrevation:unresolvedAbbrevations){
  			String query="SELECT DISTINCT urn FROM id_names NATURAL JOIN names NATURAL JOIN urns WHERE name="+dbString(abbrevation)+" AND urn like '%kegg%'";
  			try {
  			ResultSet rs=st.executeQuery(query);
  				if (rs.next()){
  					System.out.println(abbrevation);
  					System.out.println("...may belong to "+rs.getString(1));
  					while (rs.next())	System.out.println("...may belong to "+rs.getString(1));
  			}
  			rs.close();
  			} catch (SQLException e){
  				Tools.warn("Error on "+query);
  				throw e;
  			}
  		}
  		st.close();
  	}

		public static TreeMap<URN, TreeSet<URL>> getDecisionsForKeggUrls() throws SQLException, DataFormatException, IOException {
			Tools.startMethod("getDecisionsForKeggUrls()");
			String query="SELECT keyphrase FROM decisions WHERE keyphrase like '%:kegg.%'";
			TreeMap<URN,TreeSet<URL>> map=new TreeMap<URN, TreeSet<URL>>(ObjectComparator.get());
			try {
				Statement st=createStatement(); // read the keyphrases
				ResultSet rs=st.executeQuery(query);
				while (rs.next()){ // for each keyphrase:
					TreeSet<URL> urls=Tools.URLSet();
					String key=rs.getString(1);
					String[] parts = key.replace("[", "").replace("]", "").split("<|>|,"); // split into parts
					KeggUrn urn=null;
					for (String part:parts) {
						part=part.trim();
						if (part.startsWith("urn")) { // extract urns
							urn=urnForComponent(keggIdFrom(part));
						} else urls.add(new URL(part.trim())); // extract urls
					}
					TreeSet<URL> dummy = map.get(urn); // get the urls already assigned with the urn
					if (dummy!=null) urls.addAll(dummy); // add the urls already assigned with the urn to the current list
					map.put(urn, urls); // assign the urn with the current list
				}
			} catch (SQLException e) {
				throw new SQLException(e.getMessage()+"\n\nQuery was: "+query);
			}
			Tools.endMethod(map);
			return map;
    }

		public static void setTestMode(boolean m) {
			testMode=m;
		}

		public static boolean inTestMode() {
			return testMode;
		}

		public static void storeIDrange(String rangeName, Integer firstKeggId, Integer lastKeggId) throws SQLException, IOException {
			int rangeNameId = getOrCreateNid(rangeName);
			String query="INSERT INTO id_ranges VALUES ("+rangeNameId+", "+firstKeggId+", "+lastKeggId+");";
			execute(query);
			System.out.println(rangeName + ": " + firstKeggId+"..."+lastKeggId);

    }

		public static int[] getRange(String name) throws SQLException, IOException {
			int nameId=getOrCreateNid(name);
			String query="SELECT min,max FROM id_ranges WHERE nid="+nameId+";";
			int[] result=new int[2];			
			try {
				ResultSet rs=createStatement().executeQuery(query);
				if (rs.next()){
					result[0]=rs.getInt(1);
					result[1]=rs.getInt(2);
				}
				rs.close();
			} catch (SQLException e) {
				System.err.println(query);
				throw e;
			}
			return result;
    }
		
		/**
		 * removes all content, which contains ids larger than the given one, from the database
		 * 
		 * @param keggRange the last id, which will be not deleted
		 * 
		 * @throws SQLException
		 * @throws IOException 
		 */
		public static void cleanDb(int[] keggRange) throws SQLException, IOException {
			if (keggRange[0]==keggRange[1]) return;
			int min=Math.min(keggRange[0], keggRange[1]);
			int max=Math.max(keggRange[0], keggRange[1]);
			Statement st = InteractionDB.createStatement();
			Vector<String> queries = new Vector<String>();
			queries.add("DELETE FROM compartment_pathways WHERE cid>" + min + " AND cid<"+max);
			queries.add("DELETE FROM compartment_pathways WHERE pid>" + min + " AND pid<"+max);
			queries.add("DELETE FROM compartments WHERE id>" + min + " AND id<"+max);
			queries.add("DELETE FROM enzymes WHERE id>" + min + " AND id<"+max);
			queries.add("DELETE FROM enzymes_compartments WHERE cid>" + min + " AND cid<"+max); 
			queries.add("DELETE FROM enzymes_compartments WHERE eid>" + min + " AND cid<"+max);
			queries.add("DELETE FROM hierarchy WHERE contained>" + min + " AND contained<"+max);
			queries.add("DELETE FROM hierarchy WHERE container>" + min + " AND container<"+max);
			queries.add("DELETE FROM ids WHERE id>" + min + " AND id<"+max);
			queries.add("DELETE FROM products WHERE sid>" + min + " AND sid<"+max);
			queries.add("DELETE FROM products WHERE rid>" + min + " AND rid<"+max);
			queries.add("DELETE FROM reaction_directions WHERE rid>" + min + " AND rid<"+max);
			queries.add("DELETE FROM reaction_directions WHERE cid>" + min + " AND cid<"+max);
			queries.add("DELETE FROM reaction_enzymes WHERE rid>" + min + " AND rid<"+max);
			queries.add("DELETE FROM reaction_enzymes WHERE eid>" + min + " AND eid<"+max);
			queries.add("DELETE FROM reactions WHERE id>" + min + " AND id<"+max);
			queries.add("DELETE FROM substances WHERE id>" + min + " AND id<"+max);
			queries.add("DELETE FROM substrates WHERE sid>" + min + " AND sid<"+max);
			queries.add("DELETE FROM substrates WHERE rid>" + min + " AND rid<"+max);
			queries.add("DELETE FROM urns WHERE id>" + min + " AND id<"+max);
			try {
				while (!queries.isEmpty()) {
					System.out.println("executing " + queries.firstElement());
					st.execute(queries.firstElement());
					queries.remove(0);
				}
			} catch (SQLException e) {
				System.err.println(queries.firstElement());
				throw e;
			}
		}

		public static void cleanNames() throws SQLException, IOException {
	    execute("delete id_names.* from urns natural join id_names natural join names where urn like 'urn:miriam:kegg%' and substring(urn,-6)=name");	    
    }

		public static TreeSet<Integer> getReactionsFor(TreeSet<Integer> listed) throws SQLException, IOException {			
			String query="SELECT subs.rid"+
									" FROM (SELECT rid,sid" +
									"       FROM substrates"+
									"       UNION SELECT rid,sid" +
									"       FROM products) AS subs" +
									" WHERE subs.sid in "+setToDBset(listed)+
									" GROUP BY subs.rid"+
									" HAVING COUNT(*) ="+listed.size();
			ResultSet rs=createStatement().executeQuery(query);
			
			TreeSet<Integer> result=new TreeSet<Integer>();
			while (rs.next())	result.add(rs.getInt(1));
		  return result;
	  }

		public static Boolean isSpontan(int rid) throws SQLException, IOException {
			String query="SELECT spontan FROM reactions WHERE id="+rid;
			ResultSet rs=createStatement().executeQuery(query);
			if (rs.next()){
				return rs.getBoolean(1);
			}
	    return null;
    }
}
