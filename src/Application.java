import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class Application {

	// https://github.com/devng/ldbn/blob/master/src/main/java/se/umu/cs/ldbn/client/core/Algorithms.java
	// https://www.tutorialspoint.com/dbms/database_normalization.htm
	// https://www.cs.colostate.edu/~cs430dl/yr2019su/home_examples.php
	// https://stackoverflow.com/questions/2718420/candidate-keys-from-functional-dependencies
	// https://www.geeksforgeeks.org/normal-forms-in-dbms/

	/**
	 * Closure
	 * 
	 * Find all FD's for attributes a in a relation R
	 * 
	 * a+ denotes the set of attributes that are functionally determined by a
	 * 
	 * IF attribute(s) a IS/ARE A SUPERKEY OF R THEN a+ SHOULD BE THE WHOLE
	 * RELATION R. This is our goal. Any attributes in a relation not part of
	 * the closure indicates a problem with the design.
	 * 
	 * Algorithm for Closure
	 * 
	 * result = a; //initialize with attributes in superkey a WHILE (more
	 * changes to result) DO FOREACH ( FD b → c in R) DO IF b ⊆ result
	 * //determinant is in the set THEN result := result ∪ c //then add
	 * dependency attribute(s)
	 * 
	 * 
	 **/

	/**
	 * 
	 * 
	 * 
	 * 
	 * First Normal Form : A relation is in first normal form if every attribute
	 * in that relation is singled valued Second Normal Form: To be in second
	 * normal form, a relation must be in first normal form and relation must
	 * not contain any partial dependency. A relation is in 2NF if it has No
	 * Partial Dependency, i.e., no non-prime attribute (attributes which are
	 * not part of any candidate key) is dependent on any proper subset of any
	 * candidate key of the table. Example 2 – Consider following functional
	 * dependencies in relation R (A, B , C, D ) AB -> C [A and B together
	 * determine C] BC -> D [B and C together determine D]
	 * 
	 * In the above relation, AB is the only candidate key and there is no
	 * partial dependency, i.e., any proper subset of AB doesn’t determine any
	 * non-prime attribute.
	 * 
	 * 
	 * 
	 * Third Normal Form: ----------------
	 * 
	 * A relation is in third normal form, if there is no transitive dependency
	 * for non-prime attributes as well as it is in second normal form. A
	 * relation is in 3NF if at least one of the following condition holds in
	 * every non-trivial function dependency X –> Y
	 * 
	 * X is a super key. Y is a prime attribute (each element of Y is part of
	 * some candidate key).]
	 * 
	 * Example 2 – Consider relation R(A, B, C, D, E) A -> BC, CD -> E, B -> D,
	 * E -> A All possible candidate keys in above relation are {A, E, CD, BC}
	 * All attribute are on right sides of all functional dependencies are
	 * prime.
	 * 
	 * Boyce-Codd Normal Form (BCNF) ---------------------------- A relation R
	 * is in BCNF if R is in Third Normal Form and for every FD, LHS is super
	 * key. A relation is in BCNF iff in every non-trivial functional dependency
	 * X –> Y, X is a super key.
	 * 
	 * 
	 * 
	 * Exercise 1: Find the highest normal form in R (A, B, C, D, E) under
	 * following functional dependencies.
	 * 
	 * ABC --> D CD --> AE
	 * 
	 * Important Points for solving above type of question. 1) It is always a
	 * good idea to start checking from BCNF, then 3 NF and so on. 2) If any
	 * functional dependency satisfied a normal form then there is no need to
	 * check for lower normal form. For example, ABC –> D is in BCNF (Note that
	 * ABC is a superkey), so no need to check this dependency for lower normal
	 * forms.
	 * 
	 * Candidate keys in the given relation are {ABC, BCD}
	 * 
	 * BCNF: ABC -> D is in BCNF. Let us check CD -> AE, CD is not a super key
	 * so this dependency is not in BCNF. So, R is not in BCNF.
	 * 
	 * 3NF: ABC -> D we don’t need to check for this dependency as it already
	 * satisfied BCNF. Let us consider CD -> AE. Since E is not a prime
	 * attribute, so the relation is not in 3NF.
	 * 
	 * 2NF: In 2NF, we need to check for partial dependency. D which is a proper
	 * subset of a candidate key and it determine E, which is non-prime
	 * attribute. So, given relation is also not in 2 NF. So, the highest normal
	 * form is 1 NF.
	 * 
	 */

	/**
	 * returns union of set A and B
	 * 
	 * @param setA
	 * @param setB
	 * @return set
	 */

	public static <T> Set<T> union(Set<T> setA, Set<T> setB) {
		Set<T> tmp = new TreeSet<T>(setA);
		tmp.addAll(setB);
		return tmp;
	}

	/**
	 * returns intersection of set A and B
	 * 
	 * @param setA
	 * @param setB
	 * @return set
	 */

	public static <T> Set<T> intersection(Set<T> setA, Set<T> setB) {
		Set<T> tmp = new TreeSet<T>();
		for (T x : setA)
			if (setB.contains(x))
				tmp.add(x);
		return tmp;
	}

	/**
	 * returns set difference of set A and B
	 * 
	 * @param setA
	 * @param setB
	 * @return
	 */
	public static <T> Set<T> difference(Set<T> setA, Set<T> setB) {
		Set<T> tmp = new TreeSet<T>(setA);
		tmp.removeAll(setB);
		return tmp;
	}

	/**
	 * checks set B is subset of A
	 * 
	 * @param setA
	 * @param setB
	 * @return true or false
	 */
	public static <T> boolean isSubset(Set<T> setA, Set<T> setB) {
		return setA.containsAll(setB);
	}

	/**
	 * checks set A is super set of B
	 * 
	 * @param setA
	 * @param setB
	 * @return true or false
	 */
	public static <T> boolean isSuperSet(Set<T> setA, Set<T> setB) {
		return setA.containsAll(setB);
	}

	private static <T> boolean isMatched(Set<T> setA, Set<T> setB) {
		return !setA.isEmpty() && !setB.isEmpty() && setA.size() == setB.size() && setA.containsAll(setB);
	}

	public static boolean isNewAttributesSetInSuperSetOfAKey(Set<Character> newAttributesSets,
			Map<Set<Character>, Set<Character>> keys) {
		for (Map.Entry<Set<Character>, Set<Character>> entry : keys.entrySet()) {
			if (isSuperSet(newAttributesSets, entry.getKey())) {
				return true;
			}
		}
		return false;
	}

	public static Set<Character> getSet(String setStr) {
		Set<Character> set = new TreeSet<Character>();
		char[] chars = setStr.toCharArray();
		for (char ch : chars) {
			set.add(ch);
		}
		return set;
	}

	public static void testFindKey1() {
		Set<Character> relation = getSet("WHOSE");

		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("WH", "S"));
		functionDependencies.add(new FunctionDependency("HOS", "E"));

		/*
		 * for (Character character : relation) { Set<Character> characters =
		 * new HashSet<Character>(); characters.add(character); Set<Character>
		 * closureSet = findClosure(functionDependencies, characters);
		 * System.out.println(String.format("{%s}+-->{%s}", character,
		 * closureSet.stream().map(x ->
		 * x.toString()).collect(Collectors.joining(",")))); }
		 */

		findKeys(functionDependencies, relation);
	}

	public static void testFindKey2() {
		Set<Character> relation = getSet("ABCD");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("A", "BCD"));
		functionDependencies.add(new FunctionDependency("C", "A"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey3() {
		Set<Character> relation = getSet("ABCDEFG");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("AB", "F"));
		functionDependencies.add(new FunctionDependency("AD", "E"));
		functionDependencies.add(new FunctionDependency("F", "G"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey4() {
		Set<Character> relation = getSet("ABCD");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("ABC", "D"));
		functionDependencies.add(new FunctionDependency("D", "A"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey5() {
		Set<Character> relation = getSet("ABCDEF");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("DF", "C"));
		functionDependencies.add(new FunctionDependency("BC", "F"));
		functionDependencies.add(new FunctionDependency("E", "A"));
		functionDependencies.add(new FunctionDependency("ABC", "E"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey6() {
		Set<Character> relation = getSet("ABCDE");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("A", "BC"));
		functionDependencies.add(new FunctionDependency("CD", "E"));
		functionDependencies.add(new FunctionDependency("B", "D"));
		functionDependencies.add(new FunctionDependency("E", "A"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey7() {
		Set<Character> relation = getSet("ABCD");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("AB", "CD"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey8() {
		Set<Character> relation = getSet("ABCDE");
		Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		functionDependencies.add(new FunctionDependency("AB", "CD"));
		functionDependencies.add(new FunctionDependency("E", "A"));
		functionDependencies.add(new FunctionDependency("D", "A"));
		// functionDependencies.add(new FunctionDependency("E", "A"));

		findKeys(functionDependencies, relation);

	}

	public static void testFindKey9() {

		Relation relation = new Relation("ABCD");
		relation.addFD("ABC", "D");
		relation.addFD("D", "A");

		findKeys2(relation);
		System.out.println(relation);

	}

	public static void testFindKey10() {

		Relation relation = new Relation("ABCD");
		relation.addFD("AB", "CD");

		findKeys2(relation);

		findNormalForm(relation);

		System.out.println(relation);
	}

	public static void testFindKey11() {

		Relation relation = new Relation("ABCDE");
		relation.addFD("AB", "CD");
		relation.addFD("E", "A");
		relation.addFD("D", "A");

		findKeys2(relation);

		findNormalForm(relation);

		System.out.println(relation);
	}

	public static void testFindKey12() {

		Relation relation = new Relation("ABCD");
		relation.addFD("ABC", "D");
		relation.addFD("D", "A");

		findKeys2(relation);

		findNormalForm(relation);

		System.out.println(relation);
	}

	public static void main(String[] args) throws IOException {

		// testFindKey1();
		// testFindKey2();
		// testFindKey3();
		// testFindKey4();
		// testFindKey5();
		// testFindKey6();

		// testFindKey7();
		// testFindKey8();

		// testFindKey9();

		// testFindKey11();
		// testFindKey12();

		// Enter data using BufferReader
		BufferedReader reader = new BufferedReader(new InputStreamReader(System.in));

		// Reading data using readLine
		System.out.println("******************************************");
		System.out.println("***********Enter QUIT to exit*************");
		System.out.println("******************************************");
		while (true) {
			// get Relational attributes
			String relationStr = "";
			boolean isValidRelation = true;
			do {
				System.out.print("Enter Relation's Attributes(In Uppercase): ");
				relationStr = getUserInput(reader);
				isValidRelation = relationStr.matches("[A-Z]*");
				if (!isValidRelation) {
					System.err.println("\nWrong attributes");
				}
			} while (!isValidRelation);

			// TODO build relation with input string

			System.out.println(">>>>Enter FDs in format X->Y. Enter # to finish entering FD<<<<");
			String fdStr = "";
			boolean isFDInputDone = false;
			do {
				boolean isValidFd = true;
				do {
					System.out.print("FD: ");
					fdStr = getUserInput(reader);
					if (fdStr.equalsIgnoreCase("#")) {
						isFDInputDone = true;
					} else {
						isValidFd = fdStr.matches("[A-Z]*->[A-Z]*");
						if (!isValidFd) {
							System.err.println("\nWrong format:Enter FD in X->Y format");
						}
						
						String[] fdStrs =fdStr.split("->");
						
						Set<Character> lhsOfFD = getSetFromString(fdStrs[0]);
						Set<Character> rhsOfFD = getSetFromString(fdStrs[1]);
						if(isSubset(lhsOfFD, rhsOfFD)){
							System.err.println("\nWrong FD.");
						}
						
					}
				} while (!isValidFd || !isFDInputDone);

				// TODO build and validate relation
				System.out.println(fdStr);
			} while (!isFDInputDone);

			// TODO printout Summary of Relations and FDS
			String questionStr = "";

			do {
				System.out.println("Enter 1: to find closures");
				System.out.println("      2: to find keys and NF");
				System.out.println("      #: to start to enter new ralation");
				questionStr = getUserInput(reader);
				if (questionStr.equals("1")) {
					// TODO: find Close in loop
					System.out.println("Enter seed or # for back");
					String seedStr = "";
					do {
						System.out.print("Seed: ");
						seedStr = getUserInput(reader);
						if (!seedStr.equals("#")) {
							// TODO: find clouser for input and show the clouser
						}
					} while (!seedStr.equals("#"));

				} else if (questionStr.equals("2")) {
					// TODO: find keys and normalization
				}
			} while (!questionStr.equals("#"));

		}

	}

	private static Set<Character> getSetFromString(String string) {
		Set<Character> treeSet = new TreeSet<>();
		for(Character ch: string.toCharArray()){
			treeSet.add(ch);
		}
		return treeSet;
	}

	private static String getUserInput(BufferedReader reader) throws IOException {

		String userInput = "";

		do {
			userInput = reader.readLine();
			if (!userInput.isEmpty() && userInput.equalsIgnoreCase("quit")) {
				System.out.println("You entered QUIT to exit the application");
				System.exit(-1);
			}
		} while (userInput.isEmpty());

		return userInput;
	}

	private static void findNormalForm(Relation relation) {
		for (FunctionDependency fd : relation.functionDependencies) {
			if (isBCNF(fd, relation.keys)) {
				fd.normalForm = NormalForm.BCNF;
			} else if (is3NF(fd, relation.keys)) {
				fd.normalForm = NormalForm.THIRD_NF;
			} else if (is2NF(fd, relation.keys)) {
				fd.normalForm = NormalForm.SECOND_NF;
			} else {
				fd.normalForm = NormalForm.FIRST_NF;
			}

		}
	}

	private static Set<Character> findClosure(Set<FunctionDependency> functionDependencies, Set<Character> seeds) {

		Set<Character> closureSet = new TreeSet<Character>();
		closureSet.addAll(seeds);

		// reset fd before start
		for (FunctionDependency fd : functionDependencies) {
			fd.isTaken = false;
		}

		boolean isChanged = true;
		while (isChanged) {
			isChanged = false;
			for (FunctionDependency fd : functionDependencies) {
				if (!fd.isTaken && isSubset(closureSet, fd.attributesOfLhsOfFD)) {
					closureSet.addAll(fd.attributesOfRhsOfFD);
					fd.isTaken = true;
					isChanged = true;
				}
			}
		}

		return closureSet;
	}

	public static void findKeys(Set<FunctionDependency> fds, Set<Character> relation) {
		Set<Character> allAttributesOnBothSideOfFDs = fds.stream().map(x -> x.allAttributesOfbothSide)
				.flatMap(x -> x.stream()).collect(Collectors.toSet());
		Set<Character> attributesOnLhsSideOfFDs = fds.stream().map(x -> x.attributesOfLhsOfFD).flatMap(x -> x.stream())
				.collect(Collectors.toSet());
		Set<Character> attributesOnRhsSideOfFDs = fds.stream().map(x -> x.attributesOfRhsOfFD).flatMap(x -> x.stream())
				.collect(Collectors.toSet());

		// 1. Find the attributes that are neither on the left and right side
		Set<Character> attributesNotOnLhsOrRhsOfFDs = difference(relation, allAttributesOnBothSideOfFDs);
		System.out.println("attributesNotOnLhsOrRhsOfFDs: " + attributesNotOnLhsOrRhsOfFDs);

		// 2. Find attributes that are only on the right side
		Set<Character> attributesOnlyOnRhsOfFDs = difference(attributesOnRhsSideOfFDs, attributesOnLhsSideOfFDs);
		System.out.println("attributesOnlyOnRhsOfFDs: " + attributesOnlyOnRhsOfFDs);

		// 3. Find attributes that are only on the left side
		Set<Character> attributesOnlyOnLhsOfFDs = difference(attributesOnLhsSideOfFDs, attributesOnRhsSideOfFDs);
		System.out.println("attributesOnlyOnLhsOfFDs: " + attributesOnlyOnLhsOfFDs);

		// 4. find attributes that are on both side
		Set<Character> attributesFoundOnBothSideOfFDs = intersection(attributesOnLhsSideOfFDs,
				attributesOnRhsSideOfFDs);
		System.out.println("attributesFoundOnBothSideOfFDs: " + attributesFoundOnBothSideOfFDs);

		// 5. Combine the attributes on step 1 and 3
		Set<Character> attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs = union(attributesNotOnLhsOrRhsOfFDs,
				attributesOnlyOnLhsOfFDs);
		System.out.println("attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs: " + attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);

		Map<Set<Character>, Set<Character>> keys = new HashMap<>();

		// Test if the closures of attributes on step 5 are all the attributes
		Set<Character> closureSet = findClosure(fds, attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);
		System.out.println(String.format("%s Closure ->%s", attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs, closureSet));

		if (isMatched(relation, closureSet)) {
			// if yes declare attribute set in 5 as key
			keys.put(attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs, closureSet);
		} else {

			// if no
			Combination combination = new Combination(attributesFoundOnBothSideOfFDs);
			for (int i = 1; i <= attributesFoundOnBothSideOfFDs.size(); i++) {
				Set<Set<Character>> setofAttributes = combination.gitCombinationOfLen(i);
				for (Set<Character> characters : setofAttributes) {
					Set<Character> newAttributesSets = new TreeSet<Character>(attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);
					newAttributesSets.addAll(characters);
					// only look when new attribute set is not a supper set of
					// already discovered key
					if (!isNewAttributesSetInSuperSetOfAKey(newAttributesSets, keys)) {
						closureSet = findClosure(fds, newAttributesSets);
						System.out.println(String.format("%s Closure ->%s", newAttributesSets, closureSet));
						if (isMatched(relation, closureSet)) {
							keys.put(newAttributesSets, closureSet);
						}
					}

				}
			}
		}

		for (Map.Entry<Set<Character>, Set<Character>> entry : keys.entrySet()) {
			System.out.println(String.format("key: %s , closureset: %s", entry.getKey(), entry.getValue()));
		}

	}

	public static void findKeys2(Relation relation) {
		Set<Character> allAttributesOnBothSideOfFDs = relation.functionDependencies.stream()
				.map(x -> x.allAttributesOfbothSide).flatMap(x -> x.stream()).collect(Collectors.toSet());
		Set<Character> attributesOnLhsSideOfFDs = relation.functionDependencies.stream().map(x -> x.attributesOfLhsOfFD)
				.flatMap(x -> x.stream()).collect(Collectors.toSet());
		Set<Character> attributesOnRhsSideOfFDs = relation.functionDependencies.stream().map(x -> x.attributesOfRhsOfFD)
				.flatMap(x -> x.stream()).collect(Collectors.toSet());

		// 1. Find the attributes that are neither on the left and right side
		Set<Character> attributesNotOnLhsOrRhsOfFDs = difference(relation.attributes, allAttributesOnBothSideOfFDs);
		System.out.println("attributesNotOnLhsOrRhsOfFDs: " + attributesNotOnLhsOrRhsOfFDs);

		// 2. Find attributes that are only on the right side
		Set<Character> attributesOnlyOnRhsOfFDs = difference(attributesOnRhsSideOfFDs, attributesOnLhsSideOfFDs);
		System.out.println("attributesOnlyOnRhsOfFDs: " + attributesOnlyOnRhsOfFDs);

		// 3. Find attributes that are only on the left side
		Set<Character> attributesOnlyOnLhsOfFDs = difference(attributesOnLhsSideOfFDs, attributesOnRhsSideOfFDs);
		System.out.println("attributesOnlyOnLhsOfFDs: " + attributesOnlyOnLhsOfFDs);

		// 4. find attributes that are on both side
		Set<Character> attributesFoundOnBothSideOfFDs = intersection(attributesOnLhsSideOfFDs,
				attributesOnRhsSideOfFDs);
		System.out.println("attributesFoundOnBothSideOfFDs: " + attributesFoundOnBothSideOfFDs);

		// 5. Combine the attributes on step 1 and 3
		Set<Character> attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs = union(attributesNotOnLhsOrRhsOfFDs,
				attributesOnlyOnLhsOfFDs);
		System.out.println("attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs: " + attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);

		Map<Set<Character>, Set<Character>> keys = new HashMap<>();

		// Test if the closures of attributes on step 5 are all the attributes
		Set<Character> closureSet = findClosure(relation.functionDependencies,
				attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);
		System.out.println(String.format("%s Closure ->%s", attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs, closureSet));

		if (isMatched(relation.attributes, closureSet)) {
			// if yes declare attribute set in 5 as key
			keys.put(attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs, closureSet);
			relation.addKey(attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);
		} else {

			// if no
			Combination combination = new Combination(attributesFoundOnBothSideOfFDs);
			for (int i = 1; i <= attributesFoundOnBothSideOfFDs.size(); i++) {
				Set<Set<Character>> setofAttributes = combination.gitCombinationOfLen(i);
				for (Set<Character> characters : setofAttributes) {
					Set<Character> newAttributesSets = new TreeSet<Character>(attributesNotOnLhsOrRhsAndOnlyOnLhsOfFDs);
					newAttributesSets.addAll(characters);
					// only look when new attribute set is not a supper set of
					// already discovered key
					if (!isNewAttributesSetInSuperSetOfAKey(newAttributesSets, keys)) {
						closureSet = findClosure(relation.functionDependencies, newAttributesSets);
						System.out.println(String.format("%s Closure ->%s", newAttributesSets, closureSet));
						if (isMatched(relation.attributes, closureSet)) {
							keys.put(newAttributesSets, closureSet);
							relation.addKey(newAttributesSets);
						}
					}

				}
			}
		}

		for (Map.Entry<Set<Character>, Set<Character>> entry : keys.entrySet()) {
			System.out.println(String.format("key: %s , closureset: %s", entry.getKey(), entry.getValue()));
		}

	}

	public static class FunctionDependency {
		private final Set<Character> attributesOfLhsOfFD = new TreeSet<Character>();
		private final Set<Character> attributesOfRhsOfFD = new TreeSet<Character>();
		private final Set<Character> allAttributesOfbothSide;
		private NormalForm normalForm = NormalForm.NONE;

		private boolean isTaken;

		public FunctionDependency(String lhsOfFDStr, String rhsOfFDStr) {
			for (Character ch : lhsOfFDStr.toCharArray()) {
				this.attributesOfLhsOfFD.add(ch);
			}

			for (Character ch : rhsOfFDStr.toCharArray()) {
				this.attributesOfRhsOfFD.add(ch);
			}
			allAttributesOfbothSide = new HashSet<Character>(attributesOfLhsOfFD);
			allAttributesOfbothSide.addAll(attributesOfRhsOfFD);
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((attributesOfLhsOfFD == null) ? 0 : attributesOfLhsOfFD.hashCode());
			result = prime * result + ((attributesOfRhsOfFD == null) ? 0 : attributesOfRhsOfFD.hashCode());
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			FunctionDependency other = (FunctionDependency) obj;
			if (attributesOfLhsOfFD == null) {
				if (other.attributesOfLhsOfFD != null)
					return false;
			} else if (!attributesOfLhsOfFD.equals(other.attributesOfLhsOfFD))
				return false;
			if (attributesOfRhsOfFD == null) {
				if (other.attributesOfRhsOfFD != null)
					return false;
			} else if (!attributesOfRhsOfFD.equals(other.attributesOfRhsOfFD))
				return false;
			return true;
		}

		public Set<Character> getAttrOfBothSide() {
			return allAttributesOfbothSide;
		}

		@Override
		public String toString() {
			return "FunctionDependency [attributesOfLhsOfFD=" + attributesOfLhsOfFD + ", attributesOfRhsOfFD="
					+ attributesOfRhsOfFD + ", allAttributesOfbothSide=" + allAttributesOfbothSide + ", normalForm="
					+ normalForm.name + "]";
		}

	}

	public static boolean isBCNF(FunctionDependency fd, Set<Set<Character>> keys) {
		// A relation in in BCNF if for every non-trivial FD X → A, X is a
		// superkey
		Set<Character> lhsOfFD = fd.attributesOfLhsOfFD;
		for (Set<Character> key : keys) {
			// check LHS of fd is superkey:constains
			if (isSuperSet(lhsOfFD, key)) {
				return true;
			}
		}

		return false;

	}

	public static boolean is3NF(FunctionDependency fd, Set<Set<Character>> keys) {
		// A relation is in 3NF if for every non-trivial FD X → A, X is a
		// superkey or A is part of some key for R
		Set<Character> lhsOfFD = fd.attributesOfLhsOfFD;
		Set<Character> rhsOfFD = fd.attributesOfRhsOfFD;
		for (Set<Character> key : keys) {
			// check LHS of fd is superkey:constains
			if (isSuperSet(lhsOfFD, key)) {
				return true;
			}
			if (isSubset(key, rhsOfFD)) {
				return true;
			}
		}
		return false;
	}

	public static boolean is2NF(FunctionDependency fd, Set<Set<Character>> keys) {
		// A relation is in 3NF if for every non-trivial FD X → A, X is a
		Set<Character> lhsOfFD = fd.attributesOfLhsOfFD;
		Set<Character> rhsOfFD = fd.attributesOfRhsOfFD;
		for (Set<Character> key : keys) {
			// check LHS of fd is superkey:constains
			if (isMatched(lhsOfFD, key)) {
				return true;
			}
		}
		return false;
	}

	public static class Relation {
		private Set<Character> attributes = new TreeSet<Character>();
		private Set<FunctionDependency> functionDependencies = new LinkedHashSet<FunctionDependency>();
		private Set<Set<Character>> keys = new LinkedHashSet<Set<Character>>();
		private Set<Character> keyAttributes = new TreeSet<Character>();
		private Set<Character> nonKeyAttributes = new TreeSet<Character>();

		public Relation(String attributesStr) {
			char[] chars = attributesStr.toCharArray();
			for (char ch : chars) {
				attributes.add(ch);
				nonKeyAttributes.add(ch);
			}
		}

		public void addFD(String lhsOfFDStr, String rhsOfFDStr) {
			functionDependencies.add(new FunctionDependency(lhsOfFDStr, rhsOfFDStr));
		}

		public void addKey(Set<Character> key) {
			keys.add(key);
			keyAttributes.addAll(key);
			nonKeyAttributes.removeAll(key);
		}

		@Override
		public String toString() {
			return "Relation [attributes=" + attributes + "\n, functionDependencies: \n" + toStringFds() + "\n, keys="
					+ keys + "\n, keyAttributes=" + keyAttributes + "\n, nonKeyAttributes=" + nonKeyAttributes + "]";
		}

		public String toStringFds() {

			return functionDependencies.stream().map(x -> String.format("\t%s -> %s, NF: %s", x.attributesOfLhsOfFD,
					x.attributesOfRhsOfFD, x.normalForm.name)).collect(Collectors.joining("\n"));
		}

	}

	public static enum NormalForm {
		FIRST_NF("1NF"), SECOND_NF("2NF"), THIRD_NF("3NF"), BCNF("BCNF"), NONE("Not Identified");

		private String name;

		NormalForm(String value) {
			this.name = value;
		}

	}

}
