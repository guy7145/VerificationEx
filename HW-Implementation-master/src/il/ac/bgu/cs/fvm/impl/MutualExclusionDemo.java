package il.ac.bgu.cs.fvm.impl;

import il.ac.bgu.cs.fvm.FvmFacade;
import il.ac.bgu.cs.fvm.automata.Automaton;
import il.ac.bgu.cs.fvm.programgraph.*;
import il.ac.bgu.cs.fvm.transitionsystem.TransitionSystem;
import il.ac.bgu.cs.fvm.util.*;
import il.ac.bgu.cs.fvm.verification.*;

import java.util.*;
import java.util.regex.Pattern;

public class MutualExclusionDemo {
	private static String getCode(int pid1, int pid2) { return String.format("crit%1$d := 0;\ndo::true->skip;\n\tatomic{b%1$d := 1; x := %2$d};\n\twait%1$d := 1;\n\tif \n\t\t::b%2$d==0||x==%1$d -> skip\n\tfi;\n\twait%1$d := 0;\n\tcrit%1$d := 1;\n\tcrit%1$d := 0;\n\tb%1$d := 0\nod\n", pid1, pid2); }
	public static void main(String[] args) {
		FvmFacade fvm = FvmFacade.createInstance();
		System.out.println("MutualExclusionDemo of Peterson");

		ProgramGraph<String, String> p1Graph, p2Graph;
		ProgramGraph<Pair<String, String>, String> interleaved;
		try {
			System.out.println("Building PGs from code");
			p1Graph = fvm.programGraphFromNanoPromelaString(getCode(1, 2));
			p2Graph = fvm.programGraphFromNanoPromelaString(getCode(2, 1));
		} catch (Exception e) { e.printStackTrace(); return; }

		System.out.println("Interleaving PGs");
		interleaved = fvm.interleave(p1Graph, p2Graph);

		Set<ActionDef> actionDefs = new HashSet<>(Collections.singleton(new ParserBasedActDef()));
		Set<ConditionDef> conditionDefs = new HashSet<>(Collections.singleton(new ParserBasedCondDef()));

		System.out.println("Building TS from interleaved PGs");
		TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts = fvm.transitionSystemFromProgramGraph(interleaved, actionDefs, conditionDefs);

		System.out.println("Cleaning TS");
		ts = deleteAPs(ts);

		Set<Set<String>> all = Util.powerSet(ts.getAtomicPropositions());
		verifyAutomata("mutex", fvm, ts, genMutexAutomata(ts, all));
		verifyAutomata("starvation", fvm, ts, genStarvationAutomata(ts, all));
	}

	private static TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> deleteAPs(
			TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts) {
		Set<String> removeAps = new HashSet<>();
		Pattern p = Pattern.compile("[c|w][r,a]it[0|1] = [0|1]");
		for (String ap : ts.getAtomicPropositions()) if (!p.matcher(ap).find()) removeAps.add(ap);
		removeAps.forEach(ap -> ts.getStates().forEach(s -> ts.removeLabel(s, ap)));
		removeAps.forEach(ts::removeAtomicProposition);
		return ts;
	}

	private static Automaton<String, String> genStarvationAutomata(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts, Set<Set<String>> all) {
		System.out.println("Building starvation testing automata - process on wait will reach crit");
		Automaton<String, String> aut = new Automaton<>();

		all.forEach(l -> aut.addTransition("satiated", l, "satiated")); // both processes are satiated
		all.stream().filter(a -> a.contains("wait1 = 1")).forEach(l -> aut.addTransition("satiated", l, "starve1")); // process 1 is starving
		all.stream().filter(a -> a.contains("wait2 = 1")).forEach(l -> aut.addTransition("satiated", l, "starve2")); // process 2 is starving
		all.stream().filter(a -> !a.contains("crit1 = 1")).forEach(l -> aut.addTransition("starve1", l, "starve1")); // sink state
		all.stream().filter(a -> !a.contains("crit2 = 1")).forEach(l -> aut.addTransition("starve2", l, "starve2")); // sink state

		aut.setInitial("satiated");
		aut.setAccepting("starve1");
		aut.setAccepting("starve2");
		return aut;
	}

	private static Automaton<String, String> genMutexAutomata(TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts, Set<Set<String>> all) {
		System.out.println("Building mutex testing automata - two programs in crit");
		Automaton<String, String> aut = new Automaton<>();

		all.stream().filter(a -> !a.contains("crit1 = 1") || !a.contains("crit2 = 1")).forEach(l -> aut.addTransition("mutex", l, "mutex")); // both processes not in cs
		all.stream().filter(a -> a.contains("crit1 = 1") && a.contains("crit2 = 1")).forEach(l -> aut.addTransition("mutex", l, "no_mutex")); // both are in cs
		all.forEach(l -> aut.addTransition("no_mutex", l, "no_mutex")); // sink state

		aut.setInitial("mutex");
		aut.setAccepting("no_mutex");
		return aut;
	}

	private static void verifyAutomata(String name, FvmFacade fvm, TransitionSystem<Pair<Pair<String, String>, Map<String, Object>>, String, String> ts, Automaton<String, String> aut) {
		System.out.print(String.format("Verifying %s: ", name));
		VerificationResult<Pair<Pair<String, String>, Map<String, Object>>> StarvationResult = fvm.verifyAnOmegaRegularProperty(ts, aut);
		System.out.println(StarvationResult instanceof VerificationSucceeded ? "PASSED" : "FAILED");
	}
}