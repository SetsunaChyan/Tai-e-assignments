/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        Queue<JMethod> q = new LinkedList<>();
        callGraph.addEntryMethod(entry);
        q.offer(entry);

        while (!q.isEmpty()) {
            JMethod cur = q.poll();
            if (!callGraph.addReachableMethod(cur)) continue;

            for (Invoke invoke : callGraph.getCallSitesIn(cur)) {
                Set<JMethod> callees = resolve(invoke);
                for (JMethod m : callees) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m));
                    q.offer(m);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        CallKind kind = CallGraphs.getCallKind(callSite);
        Set<JMethod> ret = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();

        if (kind == CallKind.STATIC) {
            JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
            if (m != null && !m.isAbstract()) ret.add(m);
        }
        if (kind == CallKind.SPECIAL) {
            JMethod m = dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature());
            if (m != null && !m.isAbstract()) ret.add(m);
        }
        if (kind == CallKind.INTERFACE || kind == CallKind.VIRTUAL) {
            Queue<JClass> q = new LinkedList<>();
            Set<JClass> vis = new HashSet<>();
            q.offer(methodRef.getDeclaringClass());

            while (!q.isEmpty()) {
                JClass c = q.poll();
                if (!vis.add(c)) continue;

                JMethod m = dispatch(c, methodRef.getSubsignature());
                if (m != null && !m.isAbstract()) ret.add(m);

                if (c.isInterface()) {
                    for (JClass sub : hierarchy.getDirectImplementorsOf(c)) q.offer(sub);
                    for (JClass sub : hierarchy.getDirectSubinterfacesOf(c)) q.offer(sub);
                } else
                    for (JClass sub : hierarchy.getDirectSubclassesOf(c)) q.offer(sub);
            }
        }

        return ret;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod m = jclass.getDeclaredMethod(subsignature);
        if (m != null && !m.isAbstract()) {
            // System.out.println("Dispatch(" + jclass.toString() + "," + subsignature.toString() + ")" + " = " + m.toString());
            return m;
        }
        if (jclass.getSuperClass() == null) {
            // System.out.println("Dispatch(" + jclass.toString() + "," + subsignature.toString() + ")" + " = null");
            return null;
        }
        // System.out.print("Dispatch(" + jclass.toString() + "," + subsignature.toString() + ") = ");
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
