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

package pascal.taie.analysis.dataflow.analysis.constprop;

import com.fasterxml.jackson.databind.util.RawValue;
import fj.test.Bool;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        List<Var> params = cfg.getMethod().getIR().getParams();
        CPFact ret = new CPFact();
        for (Var v : params)
            if (canHoldInt(v)) ret.update(v, Value.getNAC());
        return ret;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((key, value) -> target.update(key, meetValue(value, target.get(key))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();

        if (v1.isUndef()) {
            if (v2.isConstant()) return Value.makeConstant(v2.getConstant());
            else if (v2.isUndef()) return Value.getUndef();
            else if (v2.isNAC()) return Value.getNAC();
        }
        if (v2.isUndef()) {
            if (v1.isConstant()) return Value.makeConstant(v1.getConstant());
            else if (v1.isUndef()) return Value.getUndef();
            else if (v1.isNAC()) return Value.getNAC();
        }
        // both constant
        if (v1.getConstant() == v2.getConstant()) return Value.makeConstant(v1.getConstant());
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (!(stmt instanceof DefinitionStmt defStmt)) {
            return out.copyFrom(in);
        }

        RValue rv = defStmt.getRValue();
        LValue lv = defStmt.getLValue();

        CPFact newOut = in.copy();
        if (lv instanceof Var var) {
            if (canHoldInt(var))
                newOut.update((Var) lv, evaluate(rv, in));
        }

        return out.copyFrom(newOut);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var) {
            return in.get((Var) exp);
        }
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }
        if (exp instanceof BinaryExp binaryExp) {
            Value v1 = in.get(binaryExp.getOperand1());
            Value v2 = in.get(binaryExp.getOperand2());

            // coner case
            if (binaryExp instanceof ArithmeticExp aExp) {
                switch (aExp.getOperator()) {
                    case DIV:
                    case REM:
                        if (v2.isConstant() && v2.getConstant() == 0) return Value.getUndef();
                }
            }

            if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
            if (v1.isUndef() || v2.isUndef()) return Value.getUndef();
            int lhs = v1.getConstant();
            int rhs = v2.getConstant();
            int res = 0;

            if (binaryExp instanceof ArithmeticExp aExp) {
                switch (aExp.getOperator()) {
                    case ADD -> res = lhs + rhs;
                    case SUB -> res = lhs - rhs;
                    case MUL -> res = lhs * rhs;
                    case DIV -> {
                        if (rhs == 0) return Value.getUndef();
                        res = lhs / rhs;
                    }
                    case REM -> {
                        if (rhs == 0) return Value.getUndef();
                        res = lhs % rhs;
                    }
                }
            }
            else if (binaryExp instanceof ConditionExp cExp) {
                switch (cExp.getOperator()) {
                    case EQ -> res = (lhs == rhs) ? 1 : 0;
                    case NE -> res = (lhs != rhs) ? 1 : 0;
                    case GE -> res = (lhs >= rhs) ? 1 : 0;
                    case GT -> res = (lhs > rhs) ? 1 : 0;
                    case LE -> res = (lhs <= rhs) ? 1 : 0;
                    case LT -> res = (lhs < rhs) ? 1 : 0;
                }
            }
            else if (binaryExp instanceof ShiftExp sExp) {
                switch (sExp.getOperator()) {
                    case SHL -> res = lhs << rhs;
                    case SHR -> res = lhs >> rhs;
                    case USHR -> res = lhs >>> rhs;
                }
            }
            else if (binaryExp instanceof BitwiseExp bExp) {
                switch (bExp.getOperator()) {
                    case OR -> res = lhs | rhs;
                    case AND -> res = lhs & rhs;
                    case XOR -> res = lhs ^ rhs;
                }
            }
            else {
                return Value.getNAC();
            }

            return Value.makeConstant(res);
        }
        return Value.getNAC();
    }
}
