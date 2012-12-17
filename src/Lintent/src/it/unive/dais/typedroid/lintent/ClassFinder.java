package it.unive.dais.typedroid.lintent;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarInputStream;

import com.android.tools.lint.detector.api.JavaContext;

public class ClassFinder {
	
	/**
	 * Scans all classes accessible from the context class loader which belong to the given package and subpackages.
	 *
	 * @param packageName The base package
	 * @return The classes
	 * @throws ClassNotFoundException
	 * @throws IOException
	 */
	public static ArrayList<String> getAllClassesInPackage(String packageName, JavaContext context){
	    
		ArrayList<JarInputStream> jars = new ArrayList<JarInputStream>();
		ArrayList<String> classes = new ArrayList<String>();
		JarEntry entry;
		String entryName = null;

		List<File> libraries = context.getMainProject().getJavaLibraries();
		
		/* Adds Android Library to the list of jars */
		final String androidLibraryFilename = Config.ANDROID_PLATFORM_JAR_LOC;
		try {
			if (androidLibraryFilename == null) throw new RuntimeException();
			File androidLibrary = new File(androidLibraryFilename);
			if (androidLibrary.exists()) {
				libraries.add(androidLibrary);
				System.err.println("android library found: " + androidLibraryFilename);
			}
			else throw new RuntimeException();
		}
		catch (Exception e) {
			throw new RuntimeException("Couldn't find android platform library 'android.jar'. Please verify to have set an environment variable called " +
				"ANDROID_LIBRARY which references to it (common path: $ANDROID-SDKS/platforms/android-XX/android.jar).");
		}
		
		/* Loads each jar library */
		for (File f : context.getMainProject().getJavaLibraries()){
			if (f.getName().endsWith(".jar")){
				try {
					jars.add(new JarInputStream(new FileInputStream(f)));
				} catch (Exception e) {
					throw new RuntimeException("Couldn't access project library: " + f.getAbsolutePath() + ".");
				}
			}
			else{
				//TODO: Gestire librerie non-jar
				throw new RuntimeException("Unexpected project library format: " + f.getAbsolutePath() + ". Please provide a jar library.");
			}
		}
		
		/* Looks for classes with the given package inside each jar. */
		for (JarInputStream js : jars){
			try{
				for (entry = js.getNextJarEntry(); entry != null; entry = js.getNextJarEntry()){
					entryName = entry.getName().replace("/", ".");
					if (entryName.startsWith(packageName))
						if (!entryName.endsWith("."))
							classes.add(entryName.replace("$",".").replace(".class", ""));
				}
			}
			catch(IOException e){
				if (entryName != null)
					throw new RuntimeException("Couldn't access file: " + entryName + " inside JarStream: " +  js.toString() + ".");
				throw new RuntimeException("Couldn't access following JarStream: " + js.toString());
			}
		}
		
		return classes;
	}

}
