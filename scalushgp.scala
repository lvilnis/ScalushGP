/**
scalushgp.scala

This file implements a version of the Push programming language (http://hampshire.edu/lspector/push.html)
and the PushGP genetic programming system in Scala (http://scala-lang.org/).

LICENSE:

Copyright (c) 2011 Luke Vilnis

This work is based on (versions as of 11/1/2011):

Schush/SchushGP (http://hampshire.edu/lspector/schush.ss), copyright (c) 2009, 2010 Lee Spector
Clojush/ClojushGP (https://github.com/lspector/Clojush), copyright (c) 2010, 2011 Lee Spector
Rush/RushGP (https://github.com/lvilnis/RushGP), copyright (c) 2011 Luke Vilnis

which are distributed under version 3 of the GNU General Public License as published by the
Free Software Foundation, available from http://www.gnu.org/licenses/gpl.txt.

This program is free software: you can redistribute it and/or modify it under
the terms of version 3 of the GNU General Public License as published by the
Free Software Foundation, available from http://www.gnu.org/licenses/gpl.txt.

This program is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU General Public License (http://www.gnu.org/licenses/)
for more details.

CAVEAT:

I still think there may be some bugs to shake out. I need a test suite like crazy.

HOW TO USE:

Look at the example1/2/3 functions at the end of the source for a demonstration
of how to use this implementation of PushGP. To actually run the program, I recommend
Intellij IDEA Community Edition and the Scala plugin, and change it so Ctrl+Y is "Redo" and
not "Delete Line", because that will make you lose a bunch of work.

HISTORY:

10/22/2011: Started work.
11/1/2011: First version released - very very alpha, for feedback only.
11/5/2011: First working version - completed instruction set, fixed a bunch of bugs, added 3 examples
11/12/2011: Got error scaling working, and changed to use parallel constructs where appropriate

**/

package PushGp

import util.Random
import annotation.tailrec

object MainModule {

  sealed abstract class PushType[T] {
    val name: Symbol
    def getStack(ps: ProgramState): Stack[T]
    def modifyStack(ps: ProgramState, newStack: Stack[T]): ProgramState
    def unapply(ps: ProgramState): Option[Stack[T]] = Some(getStack(ps))
  }

  case object EXEC extends PushType[Program] {
    val name = 'EXEC
    def getStack(ps: ProgramState) = ps.EXEC
    def modifyStack(ps: ProgramState, newStack: Stack[Program]) = ps.copy(EXEC = newStack)
  }

  case object CODE extends PushType[Program] {
    val name = 'CODE
    def getStack(ps: ProgramState) = ps.CODE
    def modifyStack(ps: ProgramState, newStack: Stack[Program]) = ps.copy(CODE = newStack)
  }

  case object INTEGER extends PushType[Int] {
    val name = 'INTEGER
    def getStack(ps: ProgramState) = ps.INTEGER
    def modifyStack(ps: ProgramState, newStack: Stack[Int]) = ps.copy(INTEGER = newStack)
  }

  case object FLOAT extends PushType[Float] {
    val name = 'FLOAT
    def getStack(ps: ProgramState) = ps.FLOAT
    def modifyStack(ps: ProgramState, newStack: Stack[Float]) = ps.copy(FLOAT = newStack)
  }

  case object BOOLEAN extends PushType[Boolean] {
    val name = 'BOOLEAN
    def getStack(ps: ProgramState) = ps.BOOLEAN
    def modifyStack(ps: ProgramState, newStack: Stack[Boolean]) = ps.copy(BOOLEAN = newStack)
  }

  case object AUXILIARY extends PushType[Program] {
    val name = 'AUXILIARY
    def getStack(ps: ProgramState) = ps.AUXILIARY
    def modifyStack(ps: ProgramState, newStack: Stack[Program]) = ps.copy(AUXILIARY = newStack)
  }

  case class Instruction(name: Symbol) {
    implicit def convert(s: Symbol) = Instruction(s)
  }

  sealed abstract case class Literal

  case class LInt(value: Int) extends Literal

  case class LFloat(value: Float) extends Literal

  case class LBool(value: Boolean) extends Literal


  sealed abstract case class Program {
    override def toString = programToString(this)
  }

  case class PInstruction(value: Instruction) extends Program

  case class PLiteral(value: Literal) extends Program

  case class PList(value: List[Program]) extends Program


  type Stack[T] = List[T]


  sealed case class ProgramState(
    EXEC: Stack[Program] = Nil,
    CODE: Stack[Program] = Nil,
    INTEGER: Stack[Int] = Nil,
    FLOAT: Stack[Float] = Nil,
    BOOLEAN: Stack[Boolean] = Nil,
    AUXILIARY: Stack[Program] = Nil
    ) {

    def ->[T](ty: PushType[T]): Stack[T] =
      ty.getStack(this)

    def set[T](p: (PushType[T], Stack[T])): ProgramState =
      p._1.modifyStack(this, p._2)

    def push[T](p: (PushType[T], T)): ProgramState =
      p._1.modifyStack(this, p._2 :: p._1.getStack(this))

    def pop[T](PUSHTYPE: PushType[T]): ProgramState =
      this match {
        case ps@PUSHTYPE(hd :: tl) => ps set (PUSHTYPE, tl)
        case _ => this
      }
  }

  case class InstructionDefinition[T <: PushType[_]]
  (
    instructionType: T,
    name: Symbol,
    definition: ProgramState => ProgramState
  )

  trait ~>[-F[_], +G[_]] {
    def apply[A](a: F[A]): G[A]
  }

  trait StackInst {
    def apply[A](a: Stack[A]): Stack[A]
  }

  trait PtypeInst {
    def as[A](p: PushType[A]): ProgramState => ProgramState
  }

  // PushGP data types

  sealed abstract class AtomGenerator

  case class Atom(p: Program) extends AtomGenerator

  case class Generator(g: () => Program) extends AtomGenerator

  case class Individual(
    program: Program,
    errors: List[Float],
    totalError: Option[Float],
    scaledError: Option[Float])

  // Instructions

  object add {

    var instructionTable: Map[String, InstructionDefinition[_ <: PushType[_]]] = Map.empty
    var instructionDefs: List[InstructionDefinition[_ <: PushType[_]]] = List.empty

    def lookupInstruction(ins: Instruction): ProgramState => ProgramState = {
      instructionTable(ins.name.name.toLowerCase).definition
    }

    def definitionToProgram(defn: InstructionDefinition[_ <: PushType[_]]) = {
      PInstruction(Instruction(Symbol(defn.instructionType.name.name + "_" + defn.name.name )))
    }

    def instructionSymbols = instructionDefs map definitionToProgram

    def registeredForType(PUSHTYPE: PushType[_]) = {
      instructionDefs filter (_.instructionType == PUSHTYPE) map definitionToProgram
    }

    def stackInstruction[S](PUSHTYPE: PushType[S])(name: Symbol)(definition: Stack[S] => Stack[S]) {
      val id = InstructionDefinition(PUSHTYPE, name, {
        case ps@PUSHTYPE(stack) => ps set (PUSHTYPE, definition(stack))
      })
      instructionDefs = id :: instructionDefs
      instructionTable = instructionTable + (((PUSHTYPE.name.name + "_" + name.name).toLowerCase, id))
    }

    def stackInstructions(name: Symbol)(defn: StackInst) {
      stackInstruction(EXEC)(name)(defn.apply)
      stackInstruction(CODE)(name)(defn.apply)
      stackInstruction(INTEGER)(name)(defn.apply)
      stackInstruction(FLOAT)(name)(defn.apply)
      stackInstruction(BOOLEAN)(name)(defn.apply)
    }

    def instructions(name: Symbol)(defn: PtypeInst) {
      instruction(EXEC)(name)(defn as EXEC)
      instruction(CODE)(name)(defn as CODE)
      instruction(INTEGER)(name)(defn as INTEGER)
      instruction(FLOAT)(name)(defn as FLOAT)
      instruction(BOOLEAN)(name)(defn as BOOLEAN)
    }

    def instruction[S](PUSHTYPE: PushType[S])(name: Symbol)(defn: ProgramState => ProgramState) {
      val id = InstructionDefinition(PUSHTYPE, name, defn)
      instructionDefs = id :: instructionDefs
      instructionTable = instructionTable + (((PUSHTYPE.name.name + "_" + name.name).toLowerCase, id))
    }
  }

  // Basic polymorphic stack instructions

  (add stackInstructions)('DUP)(new StackInst {
    def apply[A](s: Stack[A]) = s match {
      case hd :: tl => hd :: hd :: tl
      case _ => Nil
    }
  })
  (add stackInstructions)('POP)(new StackInst {
    def apply[A](s: Stack[A]):Stack[A] = s match {
      case hd :: tl => tl
      case _ => Nil
    }
  })
  (add stackInstructions)('SWAP)(new StackInst {
    def apply[A](s: Stack[A]) = s match {
      case a :: b :: tl => b :: a :: tl
      case _ => Nil
    }
  })
  (add stackInstructions)('ROT)(new StackInst {
    def apply[A](s: Stack[A]) = s match {
      case a :: b :: c :: tl => c :: a :: b :: tl
      case _ => Nil
    }
  })

  // maybe should just write all of them this way and ditch the StackInst type?
  // not much more verbose...
  // what about performance?
  (add instructions)('ROT)(new PtypeInst {
    def as[A](PUSHTYPE: PushType[A]) = {
      case ps@PUSHTYPE(a :: b :: c :: tl) => ps set (PUSHTYPE, c :: a :: b :: tl)
      case ps => ps
    }
  })

  (add stackInstructions)('FLUSH)(new StackInst {
    def apply[A](s: Stack[A]) = Nil
  })

  import math._

  // Polymorphic instructions using more than one stack

  (add instructions)('EQUAL)(new PtypeInst {
    def as[A](PUSHTYPE: PushType[A]) = {
      case ps@PUSHTYPE(a :: b :: tl) => ps set (PUSHTYPE, tl) push (BOOLEAN, a == b)
      case ps => ps
    }
  })
  (add instructions)('STACKDEPTH)(new PtypeInst {
    def as[A](PUSHTYPE: PushType[A]) = ps =>
      ps push(INTEGER, (ps->PUSHTYPE).length)
  })
  (add instructions)('YANK)(new PtypeInst {
    def as[A](PUSHTYPE: PushType[A]) = {
      case ps@INTEGER(rawYankIndex :: _) =>
        (ps pop INTEGER) match {
          case ps@PUSHTYPE(Nil) => ps
          case ps@PUSHTYPE(stk) =>
            val yankIndex = rawYankIndex min (stk.length - 1) max 0
            val item = stk(yankIndex)
            ps set (PUSHTYPE, item :: (stk take yankIndex) ::: (stk drop (yankIndex + 1)))
        }
      case ps => ps
    }
  })
  (add instructions)('YANKDUP)(new PtypeInst {
    def as[A](PUSHTYPE: PushType[A]) = {
      case ps@INTEGER(rawYankIndex :: _) =>
        (ps pop INTEGER) match {
          case ps@PUSHTYPE(Nil) => ps
          case ps@PUSHTYPE(stk) =>
            val yankIndex = rawYankIndex min (stk.length - 1) max 0
            (ps: ProgramState) set (PUSHTYPE, stk(yankIndex) :: stk)
        }
      case ps => ps
    }
  })

  // Arithmetic instructions

  def binop[T](PUSHTYPE: PushType[T])(op: (T, T) => T): ProgramState => ProgramState = {
    case ps@PUSHTYPE(a::b::rest) => ps set (PUSHTYPE, op(a, b)::rest)
    case ps => ps
  }

  def unop[T](PUSHTYPE: PushType[T])(op: T => T): ProgramState => ProgramState = {
    case ps@PUSHTYPE(a::rest) => ps set (PUSHTYPE, op(a)::rest)
    case ps => ps
  }

  def predBinop[T](PUSHTYPE: PushType[T])(op: (T, T) => Boolean): ProgramState => ProgramState = {
    case ps@PUSHTYPE(a::b::rest) => ps push (BOOLEAN, op(a, b)) set (PUSHTYPE, rest)
    case ps => ps
  }

  def conversion[T, U](FROMTYPE: PushType[T])(TOTYPE: PushType[U])(converter: T => U): ProgramState => ProgramState = {
    case ps@FROMTYPE(a::_) => ps pop FROMTYPE push (TOTYPE, converter(a))
    case ps => ps
  }

  (add instruction FLOAT)('ADD)(binop(FLOAT)(_ + _))
  (add instruction INTEGER)('ADD)(binop(INTEGER)(_ + _))

  (add instruction FLOAT)('SUB)(binop(FLOAT)(_ - _))
  (add instruction INTEGER)('SUB)(binop(INTEGER)(_ - _))

  (add instruction FLOAT)('MULT)(binop(FLOAT)(_ * _))
  (add instruction INTEGER)('MULT)(binop(INTEGER)(_ * _))

  (add instruction FLOAT)('MIN)(binop(FLOAT)(min(_, _)))
  (add instruction INTEGER)('MIN)(binop(INTEGER)(min(_, _)))

  (add instruction FLOAT)('MAX)(binop(FLOAT)(max(_, _)))
  (add instruction INTEGER)('MAX)(binop(INTEGER)(max(_, _)))

  (add instruction INTEGER)('MOD) {
    case ps@INTEGER(_::0::_) => ps
    case ps@INTEGER(a::b::rest) => ps set (INTEGER, (a % b) :: rest)
    case ps => ps
  }

  (add instruction FLOAT)('DIV) {
    case ps@FLOAT(_::0.0f::_) => ps
    case ps@FLOAT(a::b::rest) => ps set (FLOAT, (a / b) :: rest)
    case ps => ps
  }

  (add instruction FLOAT)('SIN)(unop(FLOAT)(fl => sin(fl).asInstanceOf[Float]))
  (add instruction FLOAT)('COS)(unop(FLOAT)(fl => cos(fl).asInstanceOf[Float]))
  (add instruction FLOAT)('TAN)(unop(FLOAT)(fl => tan(fl).asInstanceOf[Float]))

  (add instruction FLOAT)('>)(predBinop(FLOAT)(_ > _))
  (add instruction INTEGER)('>)(predBinop(INTEGER)(_ > _))

  (add instruction FLOAT)('<)(predBinop(FLOAT)(_ < _))
  (add instruction INTEGER)('<)(predBinop(INTEGER)(_ < _))

  (add instruction FLOAT)('FROMBOOLEAN)(conversion(BOOLEAN)(FLOAT)(a => if (a) 1f else 0f))
  (add instruction INTEGER)('FROMBOOLEAN)(conversion(BOOLEAN)(INTEGER)(a => if (a) 1 else 0))

  (add instruction FLOAT)('FROMINTEGER)(conversion(INTEGER)(FLOAT)(a => int2float(a)))
  (add instruction INTEGER)('FROMFLOAT)(conversion(FLOAT)(INTEGER)(a => a.asInstanceOf[Int]))

  // Boolean instructions

  (add instruction BOOLEAN)('AND)(binop(BOOLEAN)(_ && _))
  (add instruction BOOLEAN)('OR)(binop(BOOLEAN)(_ || _))
  (add instruction BOOLEAN)('NOT)(unop(BOOLEAN)( !_ ))

  (add instruction BOOLEAN)('FROMINTEGER)(conversion(INTEGER)(BOOLEAN)(_ == 0f))
  (add instruction BOOLEAN)('FROMFLOAT)(conversion(FLOAT)(BOOLEAN)(_ == 0))

  // Implicit conversions to Program ADT and helpers for writing Program literals
  
  implicit def convert(s: Symbol) = PInstruction(Instruction(s))
  implicit def convert(s: Int) = PLiteral(LInt(s))
  implicit def convert(s: Float) = PLiteral(LFloat(s))
  implicit def convert(s: Boolean) = PLiteral(LBool(s))
  implicit def convert(s: List[Program]) = PList(s)
  implicit def convert(s: PList) = s.value
  def p(plist: Program*) = PList(plist.toList)

  // Code and Exec specific instructions

  (add instruction EXEC)('Y) {
    case ps@EXEC(x :: execRest) => ps set (EXEC, p(x, 'EXEC_Y) ::: execRest)
    case ps => ps
  }
  (add instruction EXEC)('S) {
    case ps@EXEC(x :: y :: z :: execRest) => ps set (EXEC, p(x, z, p(y, z)) ::: execRest)
    case ps => ps
  }
  (add instruction EXEC)('K) {
    case ps@EXEC(x :: _ :: execRest) => ps set (EXEC, x :: execRest)
    case ps => ps
  }

  (add instruction CODE)('APPEND)(binop(CODE)(ensureList(_):::ensureList(_)))

  //(add instruction CODE)('ATOM)(unop(CODE)({ case  }))

  (add instruction CODE)('CAR) {
    case ps@CODE(PList(hd::tl)::rest) => ps set (CODE, hd::rest)
    case ps => ps
  }

  // FIXME: this isn't quite right, i think its supposed to cons on a nil for scalars (but why?)
  (add instruction CODE)('CDR) {
    case ps@CODE(PList(hd::tl)::rest) => ps set (CODE, PList(tl)::rest)
    case ps => ps
  }

  (add instruction CODE)('CONS) {
    case ps@CODE(a::b::rest) => ps set (CODE, p(a, b)::rest)
    case ps => ps
  }

  (add instruction CODE)('DO) {
    case ps@CODE(prog::_) => ps push (EXEC, PInstruction(Instruction('CODE_POP))) push (EXEC, prog)
    case ps => ps
  }

  (add instruction CODE)('DOSTAR) {
    case ps@CODE(prog::rest) => ps set (CODE, rest) push (EXEC, prog)
    case ps => ps
  }

  (add instruction CODE)('DOSTARRANGE) { ps =>
    (ps, ps) match {
      case (CODE(toDo::codeRest), INTEGER(destIdx::curIdx::intRest)) =>
        val incr = if (curIdx < destIdx) 1 else if (destIdx > curIdx) -1 else 0
        val newState = ps pop INTEGER pop CODE
        val newInstr = if (incr == 0) toDo else
          p(curIdx + incr, destIdx, 'CODE_QUOTE, toDo, 'CODE_DOSTARRANGE)
        newState push (EXEC, newInstr)
      case _ => ps
    }
  }

  (add instruction EXEC)('DOSTARRANGE) { ps =>
    (ps, ps) match {
      case (EXEC(toDo::codeRest), INTEGER(destIdx::curIdx::intRest)) =>
        val incr = if (curIdx < destIdx) 1 else if (destIdx > curIdx) -1 else 0
        val newState = ps pop INTEGER pop EXEC
        val newInstr = if (incr == 0) toDo else
          p(curIdx + incr, destIdx, 'EXEC_DOSTARRANGE, toDo)
        newState push (EXEC, newInstr)
      case _ => ps
    }
  }

  (add instruction CODE)('FROMBOOLEAN)(conversion(BOOLEAN)(CODE)(t => t))
  (add instruction CODE)('FROMINTEGER)(conversion(INTEGER)(CODE)(t => t))
  (add instruction CODE)('FROMFLOAT)(conversion(FLOAT)(CODE)(t => t))

  (add instruction CODE)('QUOTE) {
    case ps@EXEC(prog::_) => ps push (CODE, prog) pop EXEC
    case ps => ps
  }

  (add instruction CODE)('IF) { ps =>
    (ps, ps) match {
      case (CODE(a::b::codeRest), BOOLEAN(cond::_)) =>
        ps pop BOOLEAN set (CODE, codeRest) push (EXEC, if (cond) a else b)
      case _ => ps
    }
  }

  (add instruction EXEC)('IF) { ps =>
    (ps, ps) match {
      case (EXEC(a::b::execRest), BOOLEAN(cond::boolRest)) =>
        ps pop BOOLEAN pop EXEC push (EXEC, if (cond) a else b)
      case _ => ps
    }
  }

  (add instruction CODE)('LENGTH) {
    case ps@CODE(prog::_) => ps push (INTEGER, ensureList(prog).length) pop CODE
    case ps => ps
  }

  (add instruction CODE)('LIST) {
    case ps@CODE(a::b::rest) => ps set (CODE, p(b, a)::rest)
    case ps => ps
  }

  (add instruction CODE)('NOOP) { ps => ps }
  (add instruction EXEC)('NOOP) { ps => ps }

  (add instruction CODE)('MEMBER) {
    case ps@CODE(a::b::rest) => ps set (CODE, rest) push (BOOLEAN, ensureList(a) contains b)
    case ps => ps
  }

  (add instruction CODE)('NULL) {
    case ps@CODE(prog::_) => ps push (BOOLEAN, prog == Nil) pop CODE
    case ps => ps
  }

  (add instruction CODE)('SIZE) {
    case ps@CODE(prog::_) => ps push (INTEGER, countPoints(prog)) pop CODE
    case ps => ps
  }

  // these consts are everywhere, round em up already...
  val MAX_GENERATIONS = 1000

  // Utilities

  // Should I try to implement some of these in terms of more general abstractions
  // like "foldprogram" or "filterprogram" ? Look into it...

  def |>[A, B](a: A, f: A => B): B = f(a)

  def countPoints: Program => Int = {
    case PList(ps) => 1 + (ps map countPoints sum)
    case _ => 1
  }

  def getCodeAtPoint(tree: Program,  pointIdx: Int) = {
    def loop(tree: Program,  pointIdx: Int, pointsSoFar: Int): Program = {
      if (pointIdx == 0) tree
      else tree match {
        case PList(Nil) => PList(Nil)
        case PList(firstSubtree::rest) =>
          val pointsInFirstSubtree = countPoints(firstSubtree)
          val newPointsSoFar = pointsSoFar + pointsInFirstSubtree
          if (pointIdx <= newPointsSoFar)
            loop(firstSubtree, pointIdx - pointsSoFar - 1, 0)
          else
            loop(rest, pointIdx, newPointsSoFar)
        case _ => tree
      }
    }
    loop(tree, abs(abs(pointIdx) % (1 max countPoints(tree))), 0)
  }
  // this should be factored somehow with the above code, I'm not sure
  // of the cleanest way though. The traversing and accumulating are quite tangled up...
  def insertCodeAtPoint(tree: Program, pointIdx: Int, newSubtree: Program) = {
    def loop(tree: Program, newSubtree: Program, pointIdx: Int, pointsSoFar: Int): Program = {
      if (pointIdx == 0) newSubtree
      else tree match {
        case PList(Nil) => PList(Nil)
        case PList(firstSubtree::rest) =>
          val pointsInFirstSubtree = countPoints(firstSubtree)
          val newPointsSoFar = pointsSoFar + pointsInFirstSubtree
          if (pointIdx <= newPointsSoFar)
            PList(loop(firstSubtree, newSubtree, pointIdx - pointsSoFar - 1, 0)::rest)
          else {
            val newTail = loop(rest, newSubtree, pointIdx, newPointsSoFar) match {
              case PList(replacedRest) => replacedRest
              case _ => Nil
            }
            PList(firstSubtree :: newTail)
          }
        case _ => newSubtree
      }
    }
    loop(tree, newSubtree, abs(abs(pointIdx) % countPoints(tree)), 0)
  }

  def removeCodeAtPoint(tree: Program, pointIdx: Int): Program = {
    val safePointIdx = abs(pointIdx % countPoints(tree))
    def removeSillyMarker24(prog: Program): Program = {
      prog match {
        case PList(ps) =>
          val noMarker = ps filter {
            case PInstruction(Instruction('sillymarker24)) => false
            case _ => true
          }
          PList(noMarker map removeSillyMarker24)
        case _ => prog
      }
    }
    (tree, safePointIdx) match {
      case (PList(Nil), _) => PList(Nil)
      case (_, 0) => PList(Nil)
      case _ =>
        removeSillyMarker24(insertCodeAtPoint(tree, safePointIdx, 'sillymarker24))
    }
  }

  def ensureList: Program => List[Program] = {
      case PList(ps) => ps
      case other => List(other)
  }

  def flattenProgram: Program => Program = {
      case PList(ps) => PList(ps map flattenProgram map ensureList flatten)
      case prog => prog
  }

  // Push interpreter

  val SAVE_TRACES = false
  val EVALPUSH_LIMIT = 1000
  val TOP_LEVEL_PUSH_CODE = false
  val TOP_LEVEL_POP_CODE = false

  @tailrec
  def execute(currentState: ProgramState, executionCount: Int, traces: List[Program], shouldPrint: Boolean): ProgramState = {
    currentState.EXEC match {
      case Nil => currentState
      case execTop::execRest =>
        val nextState = execTop match {
          case PInstruction(instr) =>
            add.lookupInstruction(instr)(currentState.copy(EXEC = execRest))
          case PLiteral(lit) =>
            val newState = currentState.copy(EXEC = execRest)
            lit match {
              case LInt(in) => newState push (INTEGER, in)
              case LFloat(fl) => newState push (FLOAT, fl)
              case LBool(bl) => newState push (BOOLEAN, bl)
            }
          case PList(ps) =>
            currentState.copy(EXEC = ps ::: execRest)
        }
        val newExecutionCount = 1 + executionCount
        val newTraces = if (SAVE_TRACES) { execTop::traces } else { traces }
        if (shouldPrint) {
          println("State after %s steps (last step: %s):" format (executionCount, execTop))
          println(nextState)
        }
        if (newExecutionCount > EVALPUSH_LIMIT) nextState
        else execute(nextState, newExecutionCount, newTraces, shouldPrint)
    }
  }

  def executeTopLevel(program: Program): ProgramState = {
    val startingState = ProgramState(EXEC = List(program), CODE = List(program))
    execute(startingState, 0, Nil, true)
  }

  def runRush(code: Program, state: ProgramState, shouldPrint: Boolean): ProgramState = {
    val stateWithPushed =
      if (TOP_LEVEL_PUSH_CODE) { state push (CODE, code) } else { state }
    val stateWithExec = stateWithPushed push (EXEC, code)
    if (shouldPrint) { println("State after 0 steps:"); println(stateWithExec) }
    val stateEvaluated = execute(stateWithExec, 0, Nil, shouldPrint)
    val stateWithPopped =
      if (TOP_LEVEL_POP_CODE) { stateEvaluated pop CODE } else { stateEvaluated }
    stateWithPopped
  }

  // PushGP

  val randGenerator = new Random()
  def randFloat() = randGenerator.nextFloat()
  def randInt(max: Int) =  if (max == 0) 0 else randGenerator.nextInt(max)
  def randIdx(prog: Program) = randInt(countPoints(prog))

  def autoSimplify(toSimplify: Program, errorFunction: Program => List[Float], steps: Int, shouldPrint: Boolean, progressInterval: Int) = {
    if (shouldPrint) { println("Auto-simplifying with starting size: " + countPoints(toSimplify).toString) }
    def randomlyRemove(program: Program) = {
      def loop(prog: Program, toRemove: Int): Program = {
        if (toRemove == 0) prog
        else removeCodeAtPoint(prog, randIdx(prog))
      }
      loop(program, 1 + randInt(2))
    }
    def randomlyFlatten(program: Program) = {
      val pointIdx = randIdx(program)
      val point = getCodeAtPoint(program, pointIdx)
      point match {
        case PList(ps) => insertCodeAtPoint(program , pointIdx, flattenProgram(point))
        case _ => program
      }
    }
    def printSimplificationReport(i: Int, errors: List[Float], prog: Program) {
      if (shouldPrint)
        println("step: %s\nprogram: %s\nerrors: %s\ntotal: %s\nsize: %s" format
                (i, prog, errors, errors.sum, countPoints(prog)))
    }
    def loop(errors: List[Float], prog: Program, step: Int): (Program, List[Float]) = {
      if (step == 0) (prog, errors) else {
        if (step % progressInterval == 0) printSimplificationReport(step, errors, prog)
        val newProgram = randInt(5) match {
          case 0 | 1 | 2 | 3 => randomlyRemove(prog)
          case 4 => randomlyFlatten(prog)
        }
        val newErrors = errorFunction(newProgram)
        val (chosenProgram, chosenErrors) =
        if (newErrors.sum > errors.sum) (prog, errors) else (newProgram, newErrors)
        loop(chosenErrors, chosenProgram, step - 1)
      }
    }
    val (simplifiedProgram, simplifiedErrors) = loop(errorFunction(toSimplify), toSimplify, steps)
    Individual(simplifiedProgram, simplifiedErrors, Some(simplifiedErrors.sum), Some(simplifiedErrors.sum))
  }

  def report(population: List[Individual], generation: Int, errorFunc: Program => List[Float], numSimplifications: Int): Individual = {
    println("\n\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;")
    println("\n;; -*- Report at generation %s" format (generation))
    val sorted = population sortBy (_.totalError getOrElse 10000f)
    val best::_ = sorted
    println("Best program: %s" format (programToString(best.program)))
    println("Partial simplification (may beat best): %s" format
            (programToString(autoSimplify(best.program, errorFunc, numSimplifications, true, 1000).program)))
    println("Errors: %s" format (best.errors))
    println("Total: %s" format (best.totalError))
    println("Scaled: %s" format (best.scaledError))
    println("Size: %s" format (countPoints(best.program)))
    println("Average total errors in population: %s" format
            ((population map (_.totalError getOrElse 10000f) sum) / population.length))
    println("Median total errors in population: %s" format
            (sorted(sorted.length / 2).totalError))
    println("Average program size in population: %s" format
            ((population map (_.program) map countPoints sum) / population.length))
    best
  }

  def generateTournamentSet(population: List[Individual], tournamentSize: Int, radius: Int, location: Int): List[Individual] = {
    def loop(tournamentSet: List[Individual], i: Int): List[Individual] = {
      if (i == 0) tournamentSet else {
        val idx =
          if (radius == 0) randInt(population.length)
          else (location + randInt(1 + 2 * radius) - radius) % population.length
        loop(population(idx)::tournamentSet, i - 1)
      }
    }
    loop(Nil, tournamentSize)
  }

  def zipWith[A,B,C](a:Seq[A])(b:Seq[B])(op:(A,B)=>C) = (a,b).zipped.map(op)

  def select(population: List[Individual], tournamentSize: Int, radius: Int, location: Int) = {
    val tournamentSet = generateTournamentSet(population, tournamentSize, radius, location)
    tournamentSet sortBy (_.scaledError) match {
      case hd::_ => hd
      case _ => error("Expected nonempty population in select!")
    }
  }

  def selectCompensatory(population: List[Individual], tournamentSize: Int, radius: Int, location: Int, firstParent: Individual) = {
    val tournamentSet = generateTournamentSet(population, tournamentSize, radius, location)
    tournamentSet sortBy (ind => zipWith(ind.errors)(firstParent.errors)(_ * _).sum) match {
      case hd::_ => hd
      case _ => error("Expected nonempty population in selectCompensatory!")
    }
  }

  // Random code generation

  def randomElement[A](xs: List[A]): A = {
    xs(randInt(xs.length))
  }

  def shuffle[A]: List[A] => List[A] = {
    case xs@(_::_) =>
      val randIndex = randInt(xs.length)
      val item = xs(randIndex)
      item :: shuffle((xs take randIndex) ::: (xs drop (randIndex + 1)))
    case _ => Nil
  }

  def decompose(number: Int, maxParts: Int): List[Int] = {
    if (maxParts <= 1 || number <= 1) List(number)
    else {
      val thisPart = 1 + randInt(number - 1)
      thisPart :: decompose(number - thisPart, maxParts - 1)
    }
  }

  def randomCodeWithSize(points: Int, atomGenerators: List[AtomGenerator]): Program = {
    if (points < 2) {
      randomElement(atomGenerators) match {
        case Atom(p) => p
        case Generator(gen) => gen()
      }
    } else {
      val elementsThisLevel = shuffle(decompose(points - 1, points - 1))
      PList(elementsThisLevel map ((in: Int) => randomCodeWithSize(in, atomGenerators)))
    }
  }

  def randomCode(maxPoints: Int, atomGenerators: List[AtomGenerator]): Program = {
    randomCodeWithSize(1 + randInt(maxPoints), atomGenerators)
  }

  // end of Random code generation

  def getNewIndividual(oldIndividual: Individual, maxPoints: Int, newProgram: Program): Individual = {
    if (countPoints(newProgram) > maxPoints) oldIndividual
    else Individual(newProgram, Nil, None, None)
  }

  def mutate(oldIndividual: Individual, mutationMaxPoints: Int, maxPoints: Int, atomGenerators: List[AtomGenerator]): Individual = {
    getNewIndividual(
      oldIndividual,
      maxPoints,
      insertCodeAtPoint(
        oldIndividual.program,
        randIdx(oldIndividual.program),
        randomCode(mutationMaxPoints, atomGenerators)))
  }

  def crossover(parent1: Individual, parent2: Individual, maxPoints: Int): Individual = {
    getNewIndividual(
      parent1,
      maxPoints,
      insertCodeAtPoint(
        parent1.program,
        randIdx(parent1.program),
        getCodeAtPoint(parent2.program, randIdx(parent2.program))))
  }

  // maybe wrap these curried versions of genetic operators in a class called GpContext or something
   // that should simplify the code a lot if the config is just passed around implicitly
  // that might make it faster at runtime so there isn't all this closure creation. so instead of passing GpConfig and currying
  // we have GpContext with GpConfig member and genetic operator methods

  def select(cfg: GpConfig)(population: List[Individual], location: Int): Individual =
    select(population, cfg.tournamentSize, cfg.trivialGeographyRadius, location)
  def selectCompensatory(cfg: GpConfig)(population: List[Individual], location: Int, parent: Individual): Individual =
    selectCompensatory(population, cfg.tournamentSize, cfg.trivialGeographyRadius, location, parent)
  def mutate(cfg: GpConfig)(individual: Individual): Individual =
    mutate(individual, cfg.mutationMaxPoints, cfg.maxPoints,  cfg.atomGenerators)
  def crossover(cfg: GpConfig)(ind1: Individual, ind2: Individual): Individual =
    crossover(ind1, ind2, cfg.maxPoints)
  def autoSimplify(cfg: GpConfig)(prog: Program, shouldPrint: Boolean, progressInterval: Int): Individual =
    autoSimplify(prog, cfg.errorFunction, cfg.reproductionSimplifications, shouldPrint, progressInterval)
  def report(cfg: GpConfig)(population: List[Individual], generation: Int): Individual =
    report(population, generation, cfg.errorFunction, cfg.reportSimplifications)

  case class GpConfig(
    errorFunction: Program => List[Float] =
      (_ => error("Need to specify an error function!")),
    errorThreshold: Float = 0,
    populationSize: Int = 1000,
    maxPoints: Int = 50,
    atomGenerators: List[AtomGenerator] =
      (add.instructionSymbols map (pr => Atom(pr): AtomGenerator)):::(
        List(
          Generator(() => randInt(100): Program),
          Generator(() => randFloat(): Program)
        ): List[AtomGenerator]) ,
    maxGenerations: Int = 1001,
    mutationProbability: Float = 0.4f,
    mutationMaxPoints: Int = 20,
    crossoverProbability: Float = 0.4f,
    simplificationProbability: Float = 0.1f,
    tournamentSize: Int = 7,
    scaleErrors: Boolean = false,
    reportSimplifications: Int = 100,
    finalReportSimplifications: Int = 1000,
    reproductionSimplifications: Int = 25,
    trivialGeographyRadius: Int = 0,
    compensatoryMateSelection: Boolean = false)

  // this is the main loop
   def pushgp(cfg: GpConfig): Option[Individual] = {
    println("Starting PushGP run.\nError function: %s\nError threshold: %s\nPopulation size: %s\nMax points: %s" format
            (cfg.errorFunction, cfg.errorThreshold, cfg.populationSize, cfg.maxPoints))
    println("Atom generators: %s\nMax generations: %s\nMutation probability: %s\nMutation max points: %s" format
            (cfg.atomGenerators, cfg.maxGenerations, cfg.mutationProbability, cfg.mutationMaxPoints))
    println("Crossover probability: %s\nSimplification probability: %s\nTournament size: %s" format
            (cfg.crossoverProbability, cfg.simplificationProbability, cfg.tournamentSize))
    println("Scale errors: %s" format (cfg.scaleErrors))
    println("Report simplifications: %s" format (cfg.reportSimplifications))
    println("Final report simplifications: %s" format (cfg.finalReportSimplifications))
    println("Reproduction simplifications: %s" format (cfg.reproductionSimplifications))
    println("Trivial geography radius: %s" format (cfg.trivialGeographyRadius))
    println("Compensatory mate selection: %s" format (cfg.compensatoryMateSelection))
    println("\n\nGenerating initial population...")

    def mainLoop(generation: Int,
                 population: List[Individual],
                 historicalTotalErrors: List[Float]): Option[Individual] = {
      println("Generation: %s" format (generation))
      if (generation <= MAX_GENERATIONS) {
        println("Computing errors...")
        val populationWithUnscaledErrors = population.par map { ind =>
          val errors = ind.errors match {
            case _ :: _ => ind.errors
            case Nil => cfg.errorFunction(ind.program)
          }
          val totalError = ind.totalError getOrElse errors.sum
          Individual(ind.program, errors, Some(totalError), Some(totalError))
        } toList
        val populationWithErrors =
          if (cfg.scaleErrors) getPopulationWithScaledErrors(cfg)(populationWithUnscaledErrors)
          else populationWithUnscaledErrors
        val best = report(cfg)(populationWithErrors, generation)
        // this is odd, don't think totalerror should be empty, this is a funky way to only add to
        // list if its not an option... nullable members in the individual class is a bad idea, we can
        // get rid of it by just separating out the first round from the main loop, then those fields will
        // always be non-null
        val newHistoricalErrors =
          historicalTotalErrors ::: (List(best.totalError) flatMap (_ map (f => List(f)) getOrElse Nil))
        if (!best.totalError.isEmpty && best.totalError.get <= cfg.errorThreshold) {
          println("\n\nSUCCESS at generation %s\nSuccessful program: %s\nErrors: %s\nTotal error: %s\nSize: %s\n" format
                  (generation, programToString(best.program), best.errors, best.totalError, countPoints(best.program)))
          val simplified = autoSimplify(cfg)(best.program, false, 1000)
          println("Simplified successful program: %s" format (programToString(simplified.program)))
          Some(simplified)
        } else {
          println("Producing offspring...")
          val newGeneration = createNewGeneration(cfg, populationWithErrors)
          mainLoop(1 + generation, newGeneration, newHistoricalErrors)
        }
      } else {
        println("FAILURE");
        None
      }
    }

    val startPopulation = 0 to cfg.populationSize map { _ =>
      Individual(randomCode(cfg.maxPoints, cfg.atomGenerators), Nil, None, None)
    }

    mainLoop(0, startPopulation.toList, Nil)
   }

  def getPopulationWithScaledErrors(cfg: GpConfig)(basePop: List[Individual]): List[Individual] = {
    println("Scaling errors...")
    val numErrorsPerIndividual = basePop.head.errors.length - 1
    val perCaseThreshold = numErrorsPerIndividual / cfg.errorThreshold
    val totalSuccessesPerErrorCase = ((0 to numErrorsPerIndividual).par map { errorIndex =>
      basePop filter (_.errors(errorIndex) <= perCaseThreshold) length
    }).toList
    basePop.par map { individual =>
      val sumScaledErrors = (0 to numErrorsPerIndividual map { errorIndex =>
        val error = individual.errors(errorIndex)
        error / (1f + totalSuccessesPerErrorCase(errorIndex))
      }).sum
      individual.copy(scaledError = Some(sumScaledErrors))
    } toList
  }

  def createNewGeneration(cfg: GpConfig, population: List[Individual]): List[Individual] = {
    // get partial sums of probabilities to create partition of [0, 1] to choose which operator
    val probs = List(cfg.mutationProbability, cfg.crossoverProbability, cfg.simplificationProbability).scan(0.0f)((_ + _))
    (0 to cfg.populationSize).par map {
      individualIdx =>
        val n = randFloat()
        val newIndividual = select(cfg)(population, individualIdx)
        if (n < probs(1))
          mutate(cfg)(newIndividual)
        else if (n < probs(2))
          crossover(cfg)(
            newIndividual,
            if (cfg.compensatoryMateSelection) selectCompensatory(cfg)(population, individualIdx, newIndividual)
            else select(cfg)(population, individualIdx))
        else if (n < probs(3))
          autoSimplify(cfg)(newIndividual.program, false, 1000)
        else
          newIndividual
    } toList
  }

  // evolve a program to model f(x) = x^2 using all instrs
  def example1(): Option[Individual] =
    pushgp(GpConfig(
      errorFunction = { program =>
        0 to 10 map { input =>
          val state = ProgramState() push (INTEGER, input)
          runRush(program, state, false) match {
            case INTEGER(topInt::intRest) => abs(topInt - (input * input)): Float
            case _ => 1000f
          }
        } toList
      }
    ))

  // evolve a program to model f(x) = x^2 using only integer instrs
  def example2(): Option[Individual] =
    pushgp(GpConfig(
      errorFunction = { program =>
        0 to 10 map { input =>
          val state = ProgramState() push (INTEGER, input)
          runRush(program, state, false) match {
            case INTEGER(topInt::intRest) => abs(topInt - (input * input)): Float
            case _ => 1000f
          }
        } toList
      },
      atomGenerators = (add registeredForType INTEGER map (pr => Atom(pr): AtomGenerator)):::(
        List(
          Generator(() => randInt(100): Program),
          Generator(() => randFloat(): Program)
        ): List[AtomGenerator])
    ))

  val testatomgens = (add registeredForType INTEGER map (pr => Atom(pr): AtomGenerator)):::(
        List(
          Generator(() => randInt(100): Program),
          Generator(() => randFloat(): Program)
        ): List[AtomGenerator])

  // evolve a program to model f(x) = f!
  // using error scaling
  def example3(): Option[Individual] = {

    (add instruction AUXILIARY)('IN) {
      case ps@AUXILIARY(PLiteral(LInt(i))::_) => ps push (INTEGER, i)
      case ps => ps
    }

    def factorial(n: Int): Int = {
      if (n < 2) 1 else n * factorial(n - 1)
    }

    pushgp(GpConfig(
      errorFunction = { program =>
        1 to 6 map { input =>
          val state = ProgramState() push (INTEGER, input) push (AUXILIARY, PLiteral(LInt(input)))
          runRush(program, state, false) match {
            case INTEGER(topInt::intRest) => abs(topInt - factorial(input)): Float
            case _ => 1000000000000f
          }
        } toList
      },
      atomGenerators = ((add.registeredForType(INTEGER):::
        add.registeredForType(EXEC):::
        add.registeredForType(BOOLEAN)) map (pr => Atom(pr): AtomGenerator)):::(
        List(
          Generator(() => randInt(100): Program),
          Generator(() => randFloat(): Program),
          Generator(() => 'AUXILIARY_IN: Program)
        ): List[AtomGenerator]),
      maxPoints = 100,
      scaleErrors = true
    ))
  }

  def programToString(prog: Program): String = {
    prog match {
      case PLiteral(lit) =>
        lit match {
          case LInt(i) => i.toString
          case LFloat(f) => f.toString + "f"
          case LBool(b) => b.toString
        }
      case PInstruction(Instruction(name)) => name.toString
      case PList(ps@(_::_)) => "(" + (ps map programToString reduceLeft (_ + " " + _)) + ")"
      case _ => "()"
    }
  }

  def main(args: Array[String]) {
    example3()
  }
}