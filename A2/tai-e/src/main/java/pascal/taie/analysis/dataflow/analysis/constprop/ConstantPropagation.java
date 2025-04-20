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

import java.util.Optional;

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

    /**
     * 边界基本块初始化, 对输入 cfg 中符合 Int 类型的 Param 初始化为 NAC
     */
    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // 初始化一个 cpf
        CPFact cpf = new CPFact();
        // 遍历 cfg 中每一个 IR 中的每一个 Var
        for(Var var: cfg.getIR().getParams()) { // getVars or getParams ?
            // 如果 Var 能够储存 Int 类型, 则初始化为 NAC
            if(canHoldInt(var)) {
                cpf.update(var, Value.getNAC());
            }
        }
        return cpf;
    }

    /**
     * 非边界基本块初始化, 默认初始化为 UNDEF
     */
    @Override
    public CPFact newInitialFact() {
        // 直接返回默认的 cpf
        return new CPFact();
    }

    /**
     * 处理 node(一个 node 对应一个 CPFact 或者 OUT) 之间的 meet 操作, 利用 meetValue 辅助函数
     */
    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // 遍历 fact 中的每一个 key(已经记录的所有 Var)
        for(Var var: fact.keySet()) {
            // 进行 meet 操作, 同时更新 target 的值
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values. 对应格上的 meet 操作, 辅助函数
     */
    public Value meetValue(Value v1, Value v2) {
       // NAC 优先级最高, 做 meet 操作都为 NAC
       if(v1.isNAC() || v2.isNAC()) {
           return Value.getNAC();
       }
       // UNDEF 优先级最低, 做 meet 操作取决于 另一个
       if(v1.isUndef()) {
           return v2;
       }
       if(v2.isUndef()) {
           return v1;
       }
       // 判断是否为确定的单一常量
       if(v1.getConstant() == v2.getConstant()) {
           // 相等则返回该常量
           return Value.makeConstant(v1.getConstant());
       } else {
           // 不相等, 说明无法确定为单一常量, 返回 NAC
           return Value.getNAC();
       }
    }

    /**
     * cfg 中节点的转移函数, 判断是否继续进行更新
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // 拷贝 in, 避免影响到 in
        CPFact tmp = in.copy();
        // 获取左值
        Optional<LValue> lv = stmt.getDef();
        // 如果左值存在
        if(lv.isPresent()) {
            // 如果左值类型为 Var 并且符合 Int 类型
            if(lv.get() instanceof Var && canHoldInt((Var)lv.get())) {
                // 计算 stmt 的右值表达式, 同时更新左值在格上的值
                tmp.update((Var)lv.get(), evaluate(((DefinitionStmt<Var, RValue>)stmt).getRValue(), in)); // 赋值语句
            }
        }
        // 将 tmp 赋值给 out, 如果有更新则返回 true, 反之则 false
        return out.copyFrom(tmp);
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
        // 1. 变量
        if(exp instanceof Var) {
            // 获取变量的值
            return in.get((Var)exp);
        }

        // 2. 常量
        if(exp instanceof IntLiteral) {
            // 直接赋值
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }

        // 3. 二元表达式
        if(exp instanceof BinaryExp) {
            // 获取两个操作数的值
            Value v1 = in.get(((BinaryExp)exp).getOperand1());
            Value v2 = in.get(((BinaryExp)exp).getOperand2());

            // DIV 和 REM 的特殊情况, 返回 UNDEF
            if(exp instanceof ArithmeticExp) {
                if(((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.DIV && v2.isConstant() && v2.getConstant() == 0) {
                    return Value.getUndef();
                }
                if(((ArithmeticExp)exp).getOperator() == ArithmeticExp.Op.REM && v2.isConstant() && v2.getConstant() == 0) {
                    return Value.getUndef();
                }
            }

            // NAC 直接返回 NAC
            if(v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }

            // UNDEF 直接返回 UNDEF
            if(v1.isUndef() || v2.isUndef()) {
                return Value.getUndef();
            }

            // 常量情况
            if(v1.isConstant() && v2.isConstant()) {
                // 1. 算术表达式
                if(exp instanceof ArithmeticExp) {
                    return switch (((ArithmeticExp)exp).getOperator()) {
                        case ADD -> Value.makeConstant(v1.getConstant() + v2.getConstant());
                        case SUB -> Value.makeConstant(v1.getConstant() - v2.getConstant());
                        case MUL -> Value.makeConstant(v1.getConstant() * v2.getConstant());
                        case DIV -> Value.makeConstant(v1.getConstant() / v2.getConstant());
                        case REM -> Value.makeConstant(v1.getConstant() % v2.getConstant());
                    };
                }
                // 2. 条件表达式
                if(exp instanceof ConditionExp) {
                    return switch (((ConditionExp)exp).getOperator()) {
                        case EQ -> Value.makeConstant(v1.getConstant() == v2.getConstant()? 1: 0);
                        case NE -> Value.makeConstant(v1.getConstant() != v2.getConstant()? 1: 0);
                        case GE -> Value.makeConstant(v1.getConstant() >= v2.getConstant()? 1: 0);
                        case GT -> Value.makeConstant(v1.getConstant() > v2.getConstant()? 1: 0);
                        case LE -> Value.makeConstant(v1.getConstant() <= v2.getConstant()? 1: 0);
                        case LT -> Value.makeConstant(v1.getConstant() < v2.getConstant()? 1: 0);
                    };
                }
                // 3. 移位表达式
                if(exp instanceof ShiftExp) {
                    return switch (((ShiftExp)exp).getOperator()) {
                        case SHL -> Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR -> Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR -> Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    };
                }
                // 4. 位运算表达式
                if(exp instanceof BitwiseExp) {
                    return switch (((BitwiseExp)exp).getOperator()) {
                        case OR -> Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case AND -> Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case XOR -> Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    };
                }
            }
            // 二元表达式的其它情况为 UNDEF
            return Value.getUndef();
        }
        // 4. 其它情况为 NAC
        return Value.getNAC();
    }
}