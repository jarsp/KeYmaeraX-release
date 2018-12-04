/**
 * Copyright (c) Carnegie Mellon University. CONFIDENTIAL
 * See LICENSE.txt for the conditions of this license.
 */
package edu.cmu.cs.ls.keymaerax.btactics

import edu.cmu.cs.ls.keymaerax.bellerophon.{BelleExpr, OnAll, PosInExpr, RenUSubst}
import edu.cmu.cs.ls.keymaerax.btactics.TactixLibrary._
import edu.cmu.cs.ls.keymaerax.btactics.FOQuantifierTactics.allInstantiateInverse
import edu.cmu.cs.ls.keymaerax.btactics.ProofRuleTactics.cut
import edu.cmu.cs.ls.keymaerax.core._
import edu.cmu.cs.ls.keymaerax.lemma.LemmaDBFactory
import edu.cmu.cs.ls.keymaerax.parser.StringConverter._
import edu.cmu.cs.ls.keymaerax.pt._
import edu.cmu.cs.ls.keymaerax.tools.ToolEvidence
import org.apache.logging.log4j.scala.Logging

import scala.collection.{immutable, mutable}
import scala.collection.immutable._
import scala.reflect.runtime.{universe => ru}

/**
 * Database of Derived Axioms.
 *
 * @author Andre Platzer
 * @see [[edu.cmu.cs.ls.keymaerax.core.AxiomBase]]
 * @note To simplify bootstrap and avoid dependency management, the proofs of the derived axioms are
 *       written with explicit reference to other scala-objects representing provables (which will be proved on demand)
 *       as opposed to by referring to the names, which needs a map canonicalName->tacticOnDemand.
 * @note Lemmas are lazy vals, since their proofs may need a fully setup prover with QE
  * @note Derived axioms use the Provable facts of other derived axioms in order to avoid initialization cycles with AxiomInfo's contract checking.
 */


object DerivedAxioms extends Logging {

  val DerivedAxiomProvableSig = ProvableSig//NoProofTermProvable
  /** Database for derived axioms */
  val derivedAxiomDB = LemmaDBFactory.lemmaDB

  type LemmaID = String

  /** A Provable proving the derived axiom/rule named id (convenience) */
  def derivedAxiomOrRule(name: String): ProvableSig = {
    val lemmaName = DerivationInfo(name) match {
      case si: StorableInfo => si.storedName
      case _ => throw new IllegalArgumentException(s"Axiom or rule $name is not storable")
    }
    require(derivedAxiomDB.contains(lemmaName), "Lemma " + lemmaName + " should already exist in the derived axioms database.")
    derivedAxiomDB.get(lemmaName).getOrElse(throw new IllegalArgumentException("Lemma " + lemmaName + " for derived axiom/rule " + name + " should have been added already")).fact
  }

  private val AUTO_INSERT = true

  /** Derive an axiom from the given provable, package it up as a Lemma and make it available */
  private[btactics] def derivedAxiom(name: String, fact: ProvableSig): Lemma = {
    require(fact.isProved, "only proved Provables would be accepted as derived axioms: " + name + " got\n" + fact)
    val lemmaName = DerivedAxiomInfo(name).storedName
    val npt = ElidingProvable(fact.underlyingProvable)
    val alternativeFact =
      if (ProvableSig.PROOF_TERMS_ENABLED) {
        TermProvable(npt, AxiomTerm(lemmaName))
      } else {
        npt
      }
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> npt.toString, "output" -> "true")) :: Nil
    // Makes it so we have the same provablesig when loading vs. storing
    val lemma = Lemma(alternativeFact, Lemma.requiredEvidence(alternativeFact, evidence), Some(lemmaName))
    if (!AUTO_INSERT) {
      lemma
    } else {
      /* @todo BUG does not work at the moment because lemmaDB adds some evidence to the lemmas and thus equality
      * (and thus contains) no longer means what this code thinks it means. */
      // first check whether the lemma DB already contains identical lemma name
      val lemmaID = if (derivedAxiomDB.contains(lemmaName)) {
        // identical lemma contents with identical name, so reuse ID
        derivedAxiomDB.get(lemmaName) match {
          case Some(storedLemma) =>
            if(storedLemma != lemma) {
              throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(lemmaName) + " (lemma " + name + " stored in file name " + lemmaName + ") instead of " + lemma )
            } else {
              lemma.name.get
            }
          case None => lemma.name.get
        }
      } else {
        derivedAxiomDB.add(lemma)
      }
      derivedAxiomDB.get(lemmaID).get
    }
  }

  private[btactics] def derivedRule(name: String, fact: ProvableSig): Lemma = {
    // create evidence (traces input into tool and output from tool)
    val evidence = ToolEvidence(immutable.List("input" -> fact.toString, "output" -> "true")) :: Nil
    val lemmaName = DerivedRuleInfo(name).storedName
    val lemma = Lemma(fact, Lemma.requiredEvidence(fact, evidence), Some(lemmaName))
    if (!AUTO_INSERT) {
      lemma
    } else {
      // first check whether the lemma DB already contains identical lemma name
      val lemmaID = if (derivedAxiomDB.contains(lemmaName)) {
        // identical lemma contents with identical name, so reuse ID
        if (derivedAxiomDB.get(lemmaName).contains(lemma)) lemma.name.get
        else {
           throw new IllegalStateException("Prover already has a different lemma filed under the same name " + derivedAxiomDB.get(lemmaName) + " (lemma " + name + " stored in file name " + lemmaName + ") instnead of " + lemma )
        }
      } else {
        derivedAxiomDB.add(lemma)
      }
      derivedAxiomDB.get(lemmaID).get
    }
  }

  private[btactics] def derivedRule(name: String, derived: Sequent, tactic: BelleExpr): Lemma =
    derivedAxiomDB.get(DerivedRuleInfo(name).storedName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        derivedRule(name, witness)
    }

  /** Derive an axiom for the given derivedAxiom with the given tactic, package it up as a Lemma and make it available */
  private[btactics] def derivedAxiom(name: String, derived: Sequent, tactic: BelleExpr): Lemma =
    derivedAxiomDB.get(DerivedAxiomInfo(name).storedName) match {
      case Some(lemma) => lemma
      case None =>
        val witness = TactixLibrary.proveBy(derived, tactic)
        assert(witness.isProved, "tactics proving derived axioms should produce proved Provables: " + name + " got\n" + witness)
        derivedAxiom(name, witness)
    }

  private val x = Variable("x_", None, Real)
  private val px = PredOf(Function("p_", None, Real, Bool), x)
  private val pany = UnitPredicational("p_", AnyArg)
  private val qx = PredOf(Function("q_", None, Real, Bool), x)
  private val qany = UnitPredicational("q_", AnyArg)
  private val fany = UnitFunctional("f_", AnyArg, Real)
  private val gany = UnitFunctional("g_", AnyArg, Real)
  private val ctxt = Function("ctx_", None, Real, Real) // function symbol
  private val ctxf = Function("ctx_", None, Real, Bool) // predicate symbol
  private val context = Function("ctx_", None, Bool, Bool) // predicational symbol

  /** populates the derived lemma database with all of the lemmas in the case statement above.*/
  private[keymaerax] def prepopulateDerivedLemmaDatabase() = {
    require(AUTO_INSERT, "AUTO_INSERT should be on if lemma database is being pre-populated.")

    val lemmas = getClass.getDeclaredFields.filter(f => classOf[Lemma].isAssignableFrom(f.getType))
    val fns = lemmas.map(_.getName)

    val mirror = ru.runtimeMirror(getClass.getClassLoader)
    // access the singleton object
    val moduleMirror = mirror.reflectModule(ru.typeOf[DerivedAxioms.type].termSymbol.asModule)
    val im = mirror.reflect(moduleMirror.instance)

    //@note lazy vals have a "hidden" getter method that does the initialization
    val fields = fns.map(fn => ru.typeOf[DerivedAxioms.type].member(ru.TermName(fn)).asMethod.getter.asMethod)
    val fieldMirrors = fields.map(im.reflectMethod)

    var failures: mutable.Buffer[(String,Throwable)] = mutable.Buffer()
    fieldMirrors.indices.foreach(idx => {
      try {
        fieldMirrors(idx)()
      } catch {
        case e: Throwable =>
          failures += (fns(idx) -> e)
          logger.warn("WARNING: Failed to add derived lemma.", e)
      }
    })
    if (failures.nonEmpty) throw new Exception(s"WARNING: Encountered ${failures.size} failures when trying to populate DerivedLemmas database. Unable to derive:\n" + failures.map(_._1).mkString("\n"), failures.head._2)
  }

  // derived rules

  /**
    * Rule "all generalization".
    * Premise p(||)
    * Conclusion \forall x p(||)
    * End.
    *
    * @derived from G or from [] monotone with program x:=*
    * @derived from Skolemize
    * @Note generalization of p(x) to p(||) as in Theorem 14
    */
  lazy val allGeneralize = derivedRule("all generalization",
    //(immutable.IndexedSeq(Sequent(immutable.Seq(), immutable.IndexedSeq(), immutable.IndexedSeq(pany))),
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("\\forall x_ p_(||)".asFormula)),
    useAt("[:*] assign nondet", PosInExpr(1::Nil))(1) &
      cut(Box(AssignAny(Variable("x_",None,Real)), True)) <(
        byUS(boxMonotone) & hide(-1) partial
        ,
        hide(1) & boxTrue(1)
        )
  )

  /**
    * Rule "Goedel".
    * Premise p(||)
    * Conclusion [a;]p(||)
    * End.
    * {{{
    *       p(||)
    *   ----------- G
    *    [a{|^@|};]p(||)
    * }}}
    * @NOTE Unsound for hybrid games
    * @derived from M and [a]true
    */
  lazy val Goedel = derivedRule("Goedel",
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("[a_{|^@|};]p_(||)".asFormula)),
    cut("[a_{|^@|};]true".asFormula) <(
      // use
      byUS(boxMonotone) & hide(-1) partial
      ,
      // show
      hide(1) & boxTrue(1)
      )
  )

  /**
    * {{{
    *   Axiom "V vacuous".
    *  p() -> [a{|^@|};]p()
    * End.
    * }}}
    * @note unsound for hybrid games
    */
  lazy val vacuousAxiom = derivedAxiom("V vacuous",
    Sequent(IndexedSeq(), IndexedSeq("p() -> [a{|^@|};]p()".asFormula)),
    useAt("VK vacuous", PosInExpr(1::Nil))(1) &
    boxTrue(1)
  )


  /**
    * Rule "CT term congruence".
    * Premise f_(||) = g_(||)
    * Conclusion ctxT_(f_(||)) = ctxT_(g_(||))
    * End.
    *
    * @derived ("Could also use CQ equation congruence with p(.)=(ctx_(.)=ctx_(g_(x))) and reflexivity of = instead.")
    */
  lazy val CTtermCongruence = derivedRule("CT term congruence",
    Sequent(immutable.IndexedSeq(), immutable.IndexedSeq("ctx_(f_(||)) = ctx_(g_(||))".asFormula)),
    cutR("ctx_(g_(||)) = ctx_(g_(||))".asFormula)(SuccPos(0)) <(
      byUS(equalReflex)
      ,
      equivifyR(1) &
        CQ(PosInExpr(0::0::Nil)) &
        useAt(equalCommute.fact)(1)
        partial
      )
  )

  /**
    * Rule "[] monotone".
    * Premise p(||) ==> q(||)
    * Conclusion [a;]p(||) ==> [a;]q(||)
    * End.
    *
    * @derived useAt("<> diamond") & by("<> monotone")
    * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
    * @see "André Platzer. Differential Hybrid Games."
    * @note Notation changed to p instead of p_ just for the sake of the derivation.
    */
  lazy val boxMonotone = derivedRule("[] monotone",
    Sequent(immutable.IndexedSeq("[a_;]p_(||)".asFormula), immutable.IndexedSeq("[a_;]q_(||)".asFormula)),
    useAt(boxAxiom.fact, PosInExpr(1::Nil))(-1) & useAt(boxAxiom.fact, PosInExpr(1::Nil))(1) &
      notL(-1) & notR(1) &
      by("<> monotone", USubst(
        SubstitutionPair(UnitPredicational("p_", AnyArg), Not(UnitPredicational("q_", AnyArg))) ::
          SubstitutionPair(UnitPredicational("q_", AnyArg), Not(UnitPredicational("p_", AnyArg))) :: Nil)) &
      notL(-1) & notR(1)
      partial
  )

  /**
    * Rule "[] monotone 2".
    * Premise q(||) ==> p(||)
    * Conclusion [a;]q(||) ==> [a;]p(||)
    * End.
    *
    * @derived useAt(boxMonotone) with p and q swapped
    * @see "André Platzer. Differential Game Logic. ACM Trans. Comput. Log. 2015"
    * @see "André Platzer. Differential Hybrid Games."
    * @note Renamed form of boxMonotone.
    */
  lazy val boxMonotone2 = derivedRule("[] monotone 2",
    Sequent(immutable.IndexedSeq("[a_;]q_(||)".asFormula), immutable.IndexedSeq("[a_;]p_(||)".asFormula)),
    useAt(boxAxiom.fact, PosInExpr(1::Nil))(-1) & useAt(boxAxiom.fact, PosInExpr(1::Nil))(1) &
      notL(-1) & notR(1) &
      byUS("<> monotone") &
      //      ProofRuleTactics.axiomatic("<> monotone", USubst(
      //        SubstitutionPair(PredOf(Function("p_", None, Real, Bool), Anything), Not(PredOf(Function("q_", None, Real, Bool), Anything))) ::
      //          SubstitutionPair(PredOf(Function("q_", None, Real, Bool), Anything), Not(PredOf(Function("p_", None, Real, Bool), Anything))) :: Nil)) &
      notL(-1) & notR(1)
      partial
  )

  /**
    * Rule "con convergence flat".
    * Premisses: \exists x_ (x <= 0 & J(||)) |- P
    *            x_ > 0, J(||) |- <a{|x_|}><x_:=x_-1;> J(||)
    * Conclusion  J(||) |- <a{|x_|}*>P(||)
    * {{{
    *    \exists x_ (x_ <= 0 & J(x_)) |- P   x_ > 0, J(x_) |- <a{|x_|}>J(x_-1)
    *    ------------------------------------------------- con
    *     J(v) |- <a{|v|}*>P
    * }}}
    */
  lazy val convergenceFlat = {
    val v = Variable("x_", None, Real)
    val anonv = ProgramConst("a_", Except(v))
    val Jany = UnitPredicational("J", AnyArg)
    derivedRule("con convergence flat",
      Sequent(immutable.IndexedSeq(Jany), immutable.IndexedSeq(Diamond(Loop(anonv), "p_(||)".asFormula))),
      cut(Diamond(Loop(anonv), Exists(immutable.Seq(v), And(LessEqual(v, Number(0)), Jany)))) <(
        hideL(-1) & mond
          // existsL(-1)
          //useAt("exists eliminate", PosInExpr(1::Nil))(-1) & andL(-1)
        ,
        hideR(1) & by(ProvableSig.rules("con convergence"))
        )
    )
  }


  // derived axioms and their proofs

  /**
    * {{{Axiom "<-> reflexive".
    *  p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val equivReflexiveAxiom = derivedAxiom("<-> reflexive",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("p_() <-> p_()".asFormula)))
    (EquivRight(SuccPos(0)), 0)
      // right branch
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (Close(AntePos(0),SuccPos(0)), 0)
  )

  /**
    * {{{Axiom "-> distributes over &".
    *  (p() -> (q()&r())) <-> ((p()->q()) & (p()->r()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val implyDistAndAxiom = derivedAxiom("-> distributes over &",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()&r_())) <-> ((p_()->q_()) & (p_()->r_()))".asFormula)),
    prop
  )

  /**
    * {{{Axiom "-> weaken".
    *  (p() -> q()) -> (p()&c() -> q())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val implWeaken = derivedAxiom("-> weaken",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) -> ((p_()&c_()) -> q_())".asFormula)),
    prop
  )

  /**
    * {{{Axiom "-> distributes over <->".
    *  (p() -> (q()<->r())) <-> ((p()->q()) <-> (p()->r()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val implyDistEquivAxiom = derivedAxiom("-> distributes over <->",
    Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_()<->r_())) <-> ((p_()->q_()) <-> (p_()->r_()))".asFormula)),
    prop
  )

  /**
    * {{{Axiom "!! double negation".
    *  (!(!p())) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val doubleNegationAxiom = derivedAxiom("!! double negation",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("(!(!p_())) <-> p_()".asFormula)))
    (EquivRight(SuccPos(0)), 0)
      // right branch
      (NotRight(SuccPos(0)), 1)
      (NotLeft(AntePos(1)), 1)
      (Close(AntePos(0),SuccPos(0)), 1)
      // left branch
      (NotLeft(AntePos(0)), 0)
      (NotRight(SuccPos(1)), 0)
      (Close(AntePos(0),SuccPos(0)), 0)
  )

  /**
    * {{{Axiom "vacuous all quantifier".
    *  (\forall x_ p()) <-> p()
    * End.
    * }}}
    *
    * @Derived from new axiom "p() -> (\forall x_ p())" and ""all instantiate" or "all eliminate".
    * @todo replace by weaker axiom in AxiomBase and prove it.
    */

  /**
    * {{{Axiom "exists dual".
    *   (!\forall x (!p(||))) <-> (\exists x p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val existsDualAxiom = derivedAxiom("exists dual",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (!p_(||))) <-> \\exists x_ p_(||)".asFormula)),
    useAt("all dual", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!exists".
    *   (!\exists x (p(x))) <-> \forall x (!p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notExists = derivedAxiom("!exists",
    Sequent(IndexedSeq(), IndexedSeq("(!\\exists x_ (p_(x_))) <-> \\forall x_ (!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom.fact, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("all dual")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!all".
    *   (!\forall x (p(||))) <-> \exists x (!p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notAll = derivedAxiom("!all",
    Sequent(IndexedSeq(), IndexedSeq("(!\\forall x_ (p_(||))) <-> \\exists x_ (!p_(||))".asFormula)),
    useAt(doubleNegationAxiom.fact, PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt(existsDualAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "![]".
    *   ![a;]p(x) <-> <a;>!p(x)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notBox = derivedAxiom("![]",
    Sequent(IndexedSeq(), IndexedSeq("(![a_;]p_(x_)) <-> (<a_;>!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom.fact, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt("<> diamond")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "!<>".
    *   !<a;>p(x) <-> [a;]!p(x)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notDiamond = derivedAxiom("!<>",
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>p_(x_)) <-> ([a_;]!p_(x_))".asFormula)),
    useAt(doubleNegationAxiom.fact, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt(boxAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "all eliminate".
    *    (\forall x p(||)) -> p(||)
    * End.
    * }}}
    *
    * @todo will clash unlike the converse proof.
    */
  lazy val allEliminateAxiom = ??? /*derivedAxiom("all eliminate",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p_(||)) -> p_(||)".asFormula)),
    US(
      USubst(SubstitutionPair(PredOf(Function("p",None,Real,Bool),DotTerm), PredOf(Function("p",None,Real,Bool),Anything))::Nil),
      Sequent(IndexedSeq(), IndexedSeq(allEliminateF)))
  )*/

  /**
    * {{{Axiom "all distribute".
    *   (\forall x (p(x)->q(x))) -> ((\forall x p(x))->(\forall x q(x)))
    * }}}
    */
  lazy val allDistributeAxiom = derivedAxiom("all distribute",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (p(x_)->q(x_))) -> ((\\forall x_ p(x_))->(\\forall x_ q(x_)))".asFormula)),
    implyR(1) & implyR(1) & allR(1) & allL(-2) & allL(-1) & prop)

  /**
    * {{{Axiom "all quantifier scope".
    *    (\forall x (p(x) & q())) <-> ((\forall x p(x)) & q())
    * End.
    * }}}
    *
    * @todo follows from "all distribute" and "all vacuous"
    */


  /**
    * {{{Axiom "[] box".
    *    (!<a;>(!p(||))) <-> [a;]p(||)
    * End.
    * }}}
    *
    * @note almost same proof as "exists dual"
    * @Derived
    */
  lazy val boxAxiom = derivedAxiom("[] box",
    Sequent(IndexedSeq(), IndexedSeq("(!<a_;>(!p_(||))) <-> [a_;]p_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{
    *   Axiom "Kd diamond modus ponens".
    *     [a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))
    *   End.
    * }}}
    */
  lazy val KdAxiom = derivedAxiom("Kd diamond modus ponens",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p(||)->q(||)) -> (<a{|^@|};>p(||) -> <a{|^@|};>q(||))".asFormula)),
    useExpansionAt("<> diamond")(1, 1::0::Nil) &
      useExpansionAt("<> diamond")(1, 1::1::Nil) &
      useAt(converseImply.fact, PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(converseImply.fact, PosInExpr(0::Nil))(1, 0::1::Nil) &
      byUS("K modal modus ponens")
  )

  /**
    * {{{
    *   Axiom "Kd2 diamond modus ponens".
    *     [a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))
    *   End.
    * }}}
    */
  lazy val Kd2Axiom = derivedAxiom("Kd2 diamond modus ponens",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};]p(||) -> (<a{|^@|};>q(||) -> <a{|^@|};>(p(||)&q(||)))".asFormula)),
    useExpansionAt("<> diamond")(1, 1::0::Nil) &
      useExpansionAt("<> diamond")(1, 1::1::Nil) &
      useAt(DerivedAxioms.converseImply, PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("K modal modus ponens", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("K modal modus ponens", PosInExpr(1::Nil))(1) &
      useAt(proveBy("(p_() -> !(p_()&q_()) -> !q_()) <-> true".asFormula, prop))(1, 1::Nil) &
      byUS("[]T system") & TactixLibrary.done
  )

  /**
    * {{{Axiom "[]~><> propagation".
    *    [a;]p(||) & <a;>q(||) -> <a;>(p(||) & q(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val boxDiamondPropagation = {
    boxAnd //@note access dependency hidden in CMon, so that it is added to the lemma database
    derivedAxiom("[]~><> propagation",
      Sequent(IndexedSeq(), IndexedSeq("([a_{|^@|};]p_(||) & <a_{|^@|};>q_(||)) -> <a_{|^@|};>(p_(||) & q_(||))".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::1::Nil) &
        useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
        cut("[a_{|^@|};]p_(||) & [a_{|^@|};]!(p_(||)&q_(||)) -> [a_{|^@|};]!q_(||)".asFormula) <(
          /* use */ prop,
          /* show */ hideR(1) &
          cut("[a_{|^@|};](p_(||) & !(p_(||)&q_(||)))".asFormula) <(
            /* use */ implyR(1) & hideL(-2) & /* monb fails renaming substitution */ implyRi & CMon(PosInExpr(1::Nil)) & prop,
            /* show */ implyR(1) & TactixLibrary.boxAnd(1) & prop
            )
          )
    )
  }

  /**
    * {{{Axiom "[]~><> subst propagation".
    *    <a;>true -> ([a;]p(||) -> <a;>p(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val boxDiamondSubstPropagation: Lemma = derivedAxiom("[]~><> subst propagation",
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>true -> ([a_{|^@|};]p(||) -> <a_{|^@|};>p(||))".asFormula)),
    cut("[a_{|^@|};]p(||) & <a_{|^@|};>true -> <a_{|^@|};>p(||)".asFormula) <(
      prop & done,
      hideR(1) & useAt(boxDiamondPropagation, PosInExpr(0::Nil))(1, 0::Nil) & useAt(andTrue)(1, 0::1::Nil) &
      prop & done
    )
  )

  /**
    * {{{Axiom "K1".
    *   [a;](p(||)&q(||)) -> [a;]p(||) & [a;]q(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K1 p. 26
    * @internal
    */
  private lazy val K1 = TactixLibrary.proveBy(//derivedAxiom("K1",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)".asFormula)),
    implyR(1) & andR(1) <(
      useAt(boxSplitLeft, PosInExpr(0::Nil))(-1) & close,
      useAt(boxSplitRight, PosInExpr(0::Nil))(-1) & close
      )
  )

  /**
    * {{{Axiom "K2".
    *   [a;]p(||) & [a;]q(||) -> [a;](p(||)&q(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K2 p. 27
    *      @internal
    */
  private lazy val K2 = TactixLibrary.proveBy(//derivedAxiom("K2",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};]p_(||) & [a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))".asFormula)),
    cut(/*(9)*/"([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||)))".asFormula) <(
      /* use */ cut(/*(6)*/"[a_{|^@|};](q_(||) -> (p_(||)&q_(||)))  ->  ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||)))".asFormula) <(
      /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
      /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
      /* show */ cut(/*(8)*/"([a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||)))  ->  (([a_{|^@|};](q_(||)->p_(||)&q_(||)) -> ([a_{|^@|};]q_(||) -> [a_{|^@|};](p_(||)&q_(||))))  ->  (([a_{|^@|};]p_(||) & [a_{|^@|};]q_(||)) -> [a_{|^@|};](p_(||)&q_(||))))".asFormula) <(
      /* use */ cut(/*(5)*/"[a_{|^@|};]p_(||) -> [a_{|^@|};](q_(||) -> p_(||)&q_(||))".asFormula) <(
      /* use */ modusPonens(AntePos(1), AntePos(0)) & close,
      /* show */ cohide(3) & useAt("K modal modus ponens", PosInExpr(1::Nil))(1) & useAt(implyTautology.fact)(1, 1::Nil) & V(1) & close
      ),
      /* show */ cohide(3) & prop
      )
      )
  )

  /**
    * {{{Axiom "K modal modus ponens &".
    *    [a;](p_(||)->q_(||)) & [a;]p_(||) -> [a;]q_(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val Kand = derivedAxiom("K modal modus ponens &",
    Sequent(IndexedSeq(), IndexedSeq("[a{|^@|};](p_(||)->q_(||)) & [a{|^@|};]p_(||) -> [a{|^@|};]q_(||)".asFormula)),
    useAt(andImplies.fact, PosInExpr(0::Nil))(1) &
    byUS("K modal modus ponens")
  )

  /**
    * {{{Axiom "&->".
    *    (A() & B() -> C()) <-> (A() -> B() -> C())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val andImplies = derivedAxiom("&->",
    Sequent(IndexedSeq(), IndexedSeq("(A_() & B_() -> C_()) <-> (A_() -> B_() -> C_())".asFormula)),
    prop)

  /**
    * {{{Axiom "[] split".
    *    [a;](p(||)&q(||)) <-> [a;]p(||)&[a;]q(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, K3 p. 28
    */
  lazy val boxAnd = derivedAxiom("[] split",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) <-> [a_{|^@|};]p_(||)&[a_{|^@|};]q_(||)".asFormula)),
    equivR(1) <(
      useAt(K1, PosInExpr(1::Nil))(1) & close,
      useAt(K2, PosInExpr(1::Nil))(1) & close
      )
  )

  /**
    * {{{Axiom "[] conditional split".
    *    [a;](p(||)->q(||)&r(||)) <-> [a;](p(||)->q(||)) & [a;](p(||)->r(||))
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val boxImpliesAnd = derivedAxiom("[] conditional split",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](P_(||)->Q_(||)&R_(||)) <-> [a_{|^@|};](P_(||)->Q_(||)) & [a_{|^@|};](P_(||)->R_(||))".asFormula)),
    useAt(implyDistAndAxiom.fact, PosInExpr(0::Nil))(1, 0::1::Nil) &
    useAt(boxAnd.fact, PosInExpr(0::Nil))(1, 0::Nil) &
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "boxSplitLeft".
    *    [a;](p(||)&q(||)) -> [a;]p(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements (1)-(5) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
    *      @internal
    */
  private lazy val boxSplitLeft = TactixLibrary.proveBy(//derivedAxiom("[] split left",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||)".asFormula)),
    cut(/*(2)*/"[a_{|^@|};](p_(||)&q_(||) -> p_(||))".asFormula) <(
      /* use */ cut(/*(4)*/"[a_{|^@|};](p_(||)&q_(||)->p_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]p_(||))".asFormula) <(
      /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
      /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
      /* show */ cohide(2) & useAt(PC1)(1, 1::0::Nil) & useAt(implySelf.fact)(1, 1::Nil) & V(1) & close
      )
  )

  /**
    * {{{Axiom "<> split".
    *    <a;>(p(||)|q(||)) <-> <a;>p(||)|<a;>q(||)
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val diamondOr = derivedAxiom("<> split",
    Sequent(IndexedSeq(), IndexedSeq("<a_{|^@|};>(p_(||)|q_(||)) <-> <a_{|^@|};>p_(||)|<a_{|^@|};>q_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(notOr.fact)(1, 0::0::1::Nil) &
      useAt(boxAnd.fact)(1, 0::0::Nil) &
      useAt(notAnd.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<> partial vacuous".
    *    <a;>p(||) & q() <-> <a;>(p(||)&q())
    * End.
    * }}}
    *
    * @Derived
    * @note unsound for hybrid games
    */
  lazy val diamondPartialVacuous: Lemma = derivedAxiom("<> partial vacuous",
    Sequent(IndexedSeq(), IndexedSeq("(<a_{|^@|};>p_(||) & q_()) <-> <a_{|^@|};>(p_(||)&q_())".asFormula)),
      equivR(1) <(
        andL(-1) & useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) &
        useAt("<> diamond", PosInExpr(1::Nil))(-1) & notL(-1) &
        useAt(notAnd.fact)(-2, 1::Nil) & useAt(implyExpand.fact, PosInExpr(1::Nil))(-2, 1::Nil) &
        useAt(converseImply.fact)(-2, 1::Nil) & useAt(doubleNegationAxiom.fact)(-2, 1::0::Nil) &
        useAt("K modal modus ponens", PosInExpr(0::Nil))(-2) & implyL(-2) <(V('Rlast) & closeId, closeId)
        ,
        useAt("<> diamond", PosInExpr(1::Nil))(-1) & useAt(notAnd.fact)(-1, 0::1::Nil) &
        useAt(implyExpand.fact, PosInExpr(1::Nil))(-1, 0::1::Nil) & notL(-1) &
        andR(1) <(
          useAt("<> diamond", PosInExpr(1::Nil))(1) & notR(1) & implyRi &
          useAt("K modal modus ponens", PosInExpr(1::Nil))(1) &
          useAt(proveBy("(!p() -> p() -> q()) <-> true".asFormula, prop))(1, 1::Nil) & byUS("[]T system")
          ,
          useAt(proveBy("!q_() -> (p_() -> !q_())".asFormula, prop), PosInExpr(1::Nil))(2, 1::Nil) &
          V(2) & notR(2) & closeId
        )
      )
  )

  /**
    * {{{Axiom "<> split left".
    *    <a;>(p(||)&q(||)) -> <a;>p(||)
    * End.
    * }}}
    *
    * @Derived
    *         @internal
    */
  private lazy val diamondSplitLeft = TactixLibrary.proveBy(//derivedAxiom("<> split left",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>(p_(||)&q_(||)) -> <a_;>p_(||)".asFormula)),
    useAt(PC1)(1, 0::1::Nil) & useAt(implySelf.fact)(1) & close
  )

  /**
    * {{{Axiom "boxSplitRight".
    *    [a;](p(||)&q(||)) -> q(||)
    * End.
    * }}}
    *
    * @Derived
    * @Note implements (6)-(9) of Cresswell, Hughes. A New Introduction to Modal Logic, K1
    *      @internal
    */
  private lazy val boxSplitRight = TactixLibrary.proveBy(//derivedAxiom("[] split right",
    Sequent(IndexedSeq(), IndexedSeq("[a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||)".asFormula)),
    cut(/*7*/"[a_{|^@|};](p_(||)&q_(||) -> q_(||))".asFormula) <(
      /* use */ cut(/*(8)*/"[a_{|^@|};](p_(||)&q_(||)->q_(||)) -> ([a_{|^@|};](p_(||)&q_(||)) -> [a_{|^@|};]q_(||))".asFormula) <(
      /* use */ modusPonens(AntePos(0), AntePos(1)) & close,
      /* show */ cohide(2) & byUS("K modal modus ponens")
      ),
      /* show */ cohide(2) & useAt(PC2)(1, 1::0::Nil) & useAt(implySelf.fact)(1, 1::Nil) & V(1) & close
      )
  )

  /**
    * {{{Axiom "[:=] assign equality exists".
    *   [x:=f();]p(||) <-> \exists x (x=f() & p(||))
    * End.
    * }}}
    *
    * @Derived by ":= assign dual" from "<:=> assign equality".
    * @todo does not derive yet
    */
//  lazy val assignbExistsAxiom =
//    derivedAxiom("[:=] assign equality exists",
//      Sequent(IndexedSeq(), IndexedSeq("[x_:=f_();]p_(||) <-> \\exists x_ (x_=f_() & p_(||))".asFormula)),
//      useAt(assigndEqualityAxiom, PosInExpr(1::Nil))(1, 1::Nil) &
//        //@note := assign dual is not applicable since [v:=t()]p(v) <-> <v:=t()>p(t),
//        //      and [v:=t()]p(||) <-> <v:=t()>p(||) not derivable since clash in allL
//        useAt(":= assign dual")(1, 1::Nil) & byUS(equivReflexiveAxiom)
//    )

  /**
    * {{{Axiom "[:=] assign exists".
    *  [x_:=f_();]p_(||) -> \exists x_ p_(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignbImpliesExistsAxiom = derivedAxiom("[:=] assign exists",
    Sequent(IndexedSeq(), IndexedSeq("[x_:=f_();]p_(||) -> \\exists x_ p_(||)".asFormula)),
//    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
//      & byUS("[:=] assign equality exists")
    useAt("[:=] assign equality exists", PosInExpr(0::Nil))(1, 0::Nil) &
    byUS(existsAndAxiom)
  )

  /**
    * {{{Axiom "[:=] assign all".
    *  \forall x_ p_(||) -> [x_:=f_();]p_(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val forallImpliesAssignbAxiom = derivedAxiom("[:=] assign all",
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> [x_:=f_();]p_(||)".asFormula)),
    //    useAt(existsAndAxiom, PosInExpr(1::Nil))(1, 1::Nil)
    //      & byUS("[:=] assign equality exists")
      useAt("[:=] assign equality", PosInExpr(0::Nil))(1, 1::Nil) &
      byUS(forallImpliesAxiom)
  )

  /**
    * {{{Axiom "\\exists& exists and".
    *  \exists x_ (q_(||) & p_(||)) -> \exists x_ (p_(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val existsAndAxiom = {
    existsEliminate //@note access dependency hidden in CMon, so that it is added to the lemma database
    derivedAxiom("\\exists& exists and",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (q_(||) & p_(||)) -> \\exists x_ (p_(||))".asFormula)),
    /*implyR(1) &*/ CMon(PosInExpr(0::Nil)) & prop // & andL(-1) & closeId//(-2,1)
  )}

  /**
    * {{{Axiom "\\forall-> forall implies".
    *  \forall x_ p_(||) -> \forall x_ (q_(||) -> p_(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val forallImpliesAxiom = {
    derivedAxiom("\\forall-> forall implies",
      Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(||) -> \\forall x_ (q_(||) -> p_(||))".asFormula)),
      /*implyR(1) &*/ CMon(PosInExpr(0::Nil)) & prop // & andL(-1) & closeId//(-2,1)
    )}

  /**
    * {{{Axiom "<:=> assign equality".
    *    <x:=f();>p(||) <-> \exists x (x=f() & p(||))
    * End.
    * }}}
    *
    * @Derived from [:=] assign equality, quantifier dualities
    * @Derived by ":= assign dual" from "[:=] assign equality exists".
    */
  lazy val assigndEqualityAxiom = derivedAxiom("<:=> assign equality",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\exists x_ (x_=f_() & p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("exists dual", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("!& deMorgan")(1, 1::0::0::Nil) &
      useAt(implyExpand.fact, PosInExpr(1::Nil))(1, 1::0::0::Nil) &
      CE(PosInExpr(0::Nil)) &
      byUS("[:=] assign equality")
  )

  /**
    * {{{Axiom "<:=> assign equality all".
    *    <x:=f();>p(||) <-> \forall x (x=f() -> p(||))
    * End.
    * }}}
    */
  lazy val assigndEqualityAllAxiom = derivedAxiom("<:=> assign equality all",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f_();>p_(||) <-> \\forall x_ (x_=f_() -> p_(||))".asFormula)),
    useAt(assignDual2Axiom.fact, PosInExpr(0::Nil))(1, 0::Nil) &
      byUS("[:=] assign equality")
  )

  /**
    * {{{Axiom "<:=> assign".
    *    <v:=t();>p(v) <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assigndAxiom = derivedAxiom("<:=> assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> p(f())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:=] assign")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> self assign".
    *    <x_:=x_;>p(||) <-> p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assigndSelfAxiom = derivedAxiom("<:=> self assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=x_;>p(||) <-> p(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:=] self assign")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom ":= assign dual".
    *    <v:=t();>p(v) <-> [v:=t();]p(v)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignDualAxiom = derivedAxiom(":= assign dual",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(x_) <-> [x_:=f();]p(x_)".asFormula)),
    useAt(assigndAxiom.fact)(1, 0::Nil) &
      useAt("[:=] assign")(1, 1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom ":= assign dual 2".
    *    <x:=f();>p(||) <-> [x:=f();]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignDual2Axiom = derivedAxiom(":= assign dual 2",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=f();>p(||) <-> [x_:=f();]p(||)".asFormula)),
    useAt("[:=] assign equality exists")(1, 1::Nil) &
      useAt("<:=> assign equality")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[:=] assign equational".
    *    [v:=t();]p(v) <-> \forall v (v=t() -> p(v))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignbEquationalAxiom = derivedAxiom("[:=] assign equational",
    Sequent(IndexedSeq(), IndexedSeq("[x_:=f();]p(x_) <-> \\forall x_ (x_=f() -> p(x_))".asFormula)),
    useAt("[:=] assign")(1, 0::Nil) &
      commuteEquivR(1) &
      byUS(allSubstitute)
  )

  /**
    * {{{Axiom "[:=] assign update".
    *    [x:=t();]p(x) <-> [x:=t();]p(x)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  lazy val assignbUpdate = derivedAxiom("[:=] assign update",
    Sequent(IndexedSeq(), IndexedSeq("[x_:=t_();]p_(x_) <-> [x_:=t_();]p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> assign update".
    *    <x:=t();>p(x) <-> <x:=t();>p(x)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */

  lazy val assigndUpdate = derivedAxiom("<:=> assign update",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=t_();>p_(x_) <-> <x_:=t_();>p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[:=] vacuous assign".
    *    [v:=t();]p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val vacuousAssignbAxiom = derivedAxiom("[:=] vacuous assign",
    Sequent(IndexedSeq(), IndexedSeq("[v_:=t_();]p_() <-> p_()".asFormula)),
    useAt("[:=] assign")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:=> vacuous assign".
    *    <v:=t();>p() <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val vacuousAssigndAxiom = derivedAxiom("<:=> vacuous assign",
    Sequent(IndexedSeq(), IndexedSeq("<v_:=t_();>p_() <-> p_()".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(vacuousAssignbAxiom.fact)(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[':=] differential assign".
    *    [x_':=f();]p(x_') <-> p(f())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignDAxiomb = DerivedAxiomProvableSig.axioms("[':=] differential assign")
  //@note the following derivation works if uniform renaming can mix BaseVariable with DifferentialSymbols.
  /*derivedAxiom("[':=] differential assign",
    Sequent(IndexedSeq(), IndexedSeq("[x_':=f();]p(x_') <-> p(f())".asFormula)),
    ProofRuleTactics.uniformRenaming(DifferentialSymbol(Variable("x_")), Variable("x_")) &
    byUS("[:=] assign")
//      useAt("[:=] assign")(1, 0::0::Nil) &
//      byUS(equivReflexiveAxiom)
  )*/

  /**
    * {{{Axiom "<':=> differential assign".
    *    <v':=t();>p(v') <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val assignDAxiom = derivedAxiom("<':=> differential assign",
    Sequent(IndexedSeq(), IndexedSeq("<x_':=f();>p(x_') <-> p(f())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[':=] differential assign", PosInExpr(0::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<:*> assign nondet".
    *    <x:=*;>p(x) <-> (\exists x p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val nondetassigndAxiom = derivedAxiom("<:*> assign nondet",
    Sequent(IndexedSeq(), IndexedSeq("<x_:=*;>p_(||) <-> (\\exists x_ p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[:*] assign nondet")(1, 0::0::Nil) &
      useAt("all dual", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<?> test".
    *    <?q();>p() <-> (q() & p())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val testdAxiom = derivedAxiom("<?> test",
    Sequent(IndexedSeq(), IndexedSeq("<?q_();>p_() <-> (q_() & p_())".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[?] test")(1, 0::0::Nil) &
      prop
  )

  /* inverse testd axiom for chase */
  lazy val invTestdAxiom = derivedAxiom("<?> invtest",
    Sequent(IndexedSeq(), IndexedSeq("(q_() & p_()) <-> <?q_();>p_()".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("[?] test")(1, 1::0::Nil) &
      prop
  )

  /* inverse testd axiom for chase */
  lazy val combineTestdAxiom = derivedAxiom("<?> combine",
    Sequent(IndexedSeq(), IndexedSeq("<?q_();><?p_();>r_() <-> <?q_()&p_();>r_()".asFormula)),
      useAt("<?> test")(1, 1::Nil) &
      useAt("<?> test")(1, 0::Nil) &
      useAt("<?> test")(1, 0::1::Nil) &
      prop
  )

  /**
    * {{{Axiom "<++> choice".
    *    <a;++b;>p(||) <-> (<a;>p(||) | <b;>p(||))
    * End.
    * }}}
    *
    * @todo first show de Morgan
    */
  lazy val choicedAxiom = derivedAxiom("<++> choice",
    Sequent(IndexedSeq(), IndexedSeq("<a_;++b_;>p_(||) <-> (<a_;>p_(||) | <b_;>p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[++] choice")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      prop
  )

  /**
    * {{{Axiom "<;> compose".
    *    <a;b;>p(||) <-> <a;><b;>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val composedAxiom = derivedAxiom("<;> compose",
    Sequent(IndexedSeq(), IndexedSeq("<a_;b_;>p_(||) <-> <a_;><b_;>p_(||)".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[;] compose")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 1::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<*> iterate".
    *    <{a;}*>p(||) <-> (p(||) | <a;><{a;}*> p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val iteratedAxiom = derivedAxiom("<*> iterate",
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> (p_(||) | <a_;><{a_;}*> p_(||))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("[*] iterate")(1, 0::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::1::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(notAnd.fact)(1, 0::Nil) & //HilbertCalculus.stepAt(1, 0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 1::1::0::1::Nil) &
      prop
  )

  /**
    * {{{Axiom "<*> approx".
    *    <a;>p(||) -> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val loopApproxd = derivedAxiom("<*> approx",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) -> <{a_;}*>p_(||)".asFormula)),
    useAt("<*> iterate")(1, 1::Nil) &
      useAt("<*> iterate")(1, 1::1::1::Nil) &
      cut("<a_;>p_(||) -> <a_;>(p_(||) | <a_;><{a_;}*>p_(||))".asFormula) <(
        /* use */ prop,
        /* show */ hideR(1) & implyR('_) & mond & prop
        )
  )

  /**
    * {{{Axiom "[*] approx".
    *    [{a;}*]p(||) -> [a;]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val loopApproxb = derivedAxiom("[*] approx",
    Sequent(IndexedSeq(), IndexedSeq("[{a_;}*]p_(||) -> [a_;]p_(||)".asFormula)),
    useAt("[*] iterate")(1, 0::Nil) &
      useAt("[*] iterate")(1, 0::1::1::Nil) &
      cut("[a_;](p_(||) & [a_;][{a_;}*]p_(||)) -> [a_;]p_(||)".asFormula) <(
        /* use */ prop,
        /* show */ hideR(1) & implyR('_) & monb & prop

        )
  )

  /**
    * {{{Axiom "II induction".
    *    [{a;}*](p(||)->[a;]p(||)) -> (p(||)->[{a;}*]p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val iiinduction = derivedAxiom("II induction",
    "==> [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||)) -> (p_(||)->[{a_{|^@|};}*]p_(||))".asSequent,
    useAt("I induction")(1, 1::1::Nil) & prop & done
  )


  /**
    * {{{Axiom "[*] merge".
    *    [{a;}*][{a;}*]p(||) <-> [{a;}*]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val loopMergeb = derivedAxiom("[*] merge",
    "==> [{a_{|^@|};}*][{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
    equivR(1) <(
      useAt("[*] iterate")(-1) & prop & done,
      implyRi & useAt(iiinduction, PosInExpr(1::Nil))(1) & G(1) & useAt("[*] iterate")(1, 0::Nil) & prop & done
    )
  )

  /**
    * {{{Axiom "<*> merge".
    *    <{a;}*><{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val loopMerged = derivedAxiom("<*> merge",
    "==> <{a_{|^@|};}*><{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
    equivR(1) <(
      useAt("<> diamond", PosInExpr(1::Nil))(1) & useAt("[*] merge", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("[] box", PosInExpr(1::Nil))(1, 0::1::Nil) & useAt("<> diamond")(1) &
        useAt("!! double negation")(1, 1::1::Nil) & closeId & done,
      useAt("<*> iterate")(1) & prop & done
    )
  )

  /**
    * {{{Axiom "[**] iterate iterate".
    *    [{a;}*;{a;}*]p(||) <-> [{a;}*]p(||)
    * End.
    * }}}
    * @see Lemma 7.6 of textbook
    * @Derived
    */
  lazy val iterateiterateb = derivedAxiom("[**] iterate iterate",
    "==> [{a_{|^@|};}*;{a_{|^@|};}*]p_(||) <-> [{a_{|^@|};}*]p_(||)".asSequent,
    useAt("[;] compose")(1, 0::Nil) & by(loopMergeb.fact)
  )

  /**
    * {{{Axiom "<**> iterate iterate".
    *    <{a;}*;{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val iterateiterated = derivedAxiom("<**> iterate iterate",
    "==> <{a_{|^@|};}*;{a_{|^@|};}*>p_(||) <-> <{a_{|^@|};}*>p_(||)".asSequent,
    useAt("<;> compose")(1, 0::Nil) & by(loopMerged.fact)
  )

  /**
    * {{{Axiom "[*-] backiterate".
    *    [{a;}*]p(||) <-> p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Lemma 7.5 in textbook
    * @Derived for programs
    */
  lazy val backiterateb = derivedAxiom("[*-] backiterate",
    "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||)".asSequent,
    equivR(1) <(
      byUS(backiteratebnecc.fact),
      by(backiteratebsuff.fact)
      )
  )

  /**
    * {{{Axiom "[*-] backiterate sufficiency".
    *    [{a;}*]p(||) <- p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Lemma 7.5 in textbook
    * @Derived for programs
    */
  lazy val backiteratebsuff = derivedAxiom("[*-] backiterate sufficiency",
    "p_(||) & [{a_{|^@|};}*][a_{|^@|};]p_(||) ==> [{a_{|^@|};}*]p_(||)".asSequent,
    andL(-1) & useAt(iiinduction.fact, PosInExpr(1::1::Nil))(1) <(
      close(-1,1)
      ,
      hideL(-1) & byUS(boxMonotone.fact) & implyR(1) & close(-1,1)
      )
  )

  /**
    * {{{Axiom "[*-] backiterate necessity".
    *    [{a;}*]p(||) -> p(||) & [{a;}*][{a;}]p(||)
    * End.
    * }}}
    * @see Figure 7.8 in textbook
    * @Derived for programs
    */
  lazy val backiteratebnecc = derivedAxiom("[*-] backiterate necessity",
    "[{b_{|^@|};}*]q_(||) ==> q_(||) & [{b_{|^@|};}*][b_{|^@|};]q_(||)".asSequent,
    andR(1) <(
      useAt("[*] iterate")(-1) & andL(-1) & close(-1,1)
      ,
      generalize("[{b_{|^@|};}*]q_(||)".asFormula)(1) <(
        useAt(iiinduction.fact, PosInExpr(1::1::Nil))(1) <(
          close(-1,1)
          ,
          G(1) & useAt("[*] iterate")(1, 0::Nil) & prop
          )
        ,
        implyRi()(-1,1) & byUS(loopApproxb.fact)
        )
      )
  )

  /**
    * {{{Axiom "Ieq induction".
    *    [{a;}*]p(||) <-> p(||) & [{a;}*](p(||)->[{a;}]p(||))
    * End.
    * }}}
    * @see Section 7.7.4 in textbook
    * @Derived for programs
    */
  lazy val Ieq = derivedAxiom("I",
    "==> [{a_{|^@|};}*]p_(||) <-> p_(||) & [{a_{|^@|};}*](p_(||)->[a_{|^@|};]p_(||))".asSequent,
    equivR(1) <(
      andR(1) <(
        iterateb(-1) & andL(-1) & close(-1,1)
        ,
        useAt(backiterateb.fact)(-1) & andL(-1) & hideL(-1) & byUS(boxMonotone.fact) & implyR(1) & close(-1,1)
        ),
      useAt(iiinduction.fact, PosInExpr(1::1::Nil))(1) & OnAll(prop & done)
      )
  )


  //@todo this is somewhat indirect. Maybe it'd be better to represent derived axioms merely as Lemma and auto-wrap them within their ApplyRule[LookupLemma] tactics on demand.
  //private def useAt(lem: ApplyRule[LookupLemma]): PositionTactic = TactixLibrary.useAt(lem.rule.lemma.fact)

  /**
    * {{{Axiom "exists generalize".
    *    p(t()) -> (\exists x p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val existsGeneralize = derivedAxiom("exists generalize",
    Sequent(IndexedSeq(), IndexedSeq("p_(f()) -> (\\exists x_ p_(x_))".asFormula)),
    useAt(existsDualAxiom.fact, PosInExpr(1::Nil))(1, 1::Nil) &
      implyR(SuccPos(0)) &
      notR(SuccPos(0)) &
      useAt("all instantiate", PosInExpr(0::Nil))(-2) &
      prop
  )

  /**
    * {{{Axiom "exists eliminate".
    *    p(||) -> (\exists x p(||))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val existsEliminate = derivedAxiom("exists eliminate",
    Sequent(IndexedSeq(), IndexedSeq("p_(||) -> (\\exists x_ p_(||))".asFormula)),
    useAt(existsDualAxiom.fact, PosInExpr(1::Nil))(1, 1::Nil) &
      implyR(1) &
      notR(1) &
      useAt("all eliminate", PosInExpr(0::Nil))(-2) &
      prop
  )

  /**
    * {{{Axiom "all substitute".
    *    (\forall x (x=t() -> p(x))) <-> p(t())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val allSubstitute = derivedAxiom("all substitute",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ (x_=t_() -> p_(x_))) <-> p_(t_())".asFormula)),
    equivR(SuccPos(0)) <(
      /* equiv left */ allL(Variable("x_"), "t_()".asTerm)(-1) & implyL(-1) <(cohide(2) & byUS(equalReflex), close),
      /* equiv right */ allR(1) & implyR(1) & eqL2R(-2)(1) & close
      )
  )

  /**
    * {{{Axiom "vacuous exists quantifier".
    *    (\exists x p()) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val vacuousExistsAxiom = derivedAxiom("vacuous exists quantifier",
    Sequent(IndexedSeq(), IndexedSeq("(\\exists x_ p_()) <-> p_()".asFormula)),
    useAt(existsDualAxiom.fact, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("vacuous all quantifier")(1, 0::0::Nil) &
      useAt(doubleNegationAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "partial vacuous exists quantifier".
    *    (\exists x p(x) & q()) <-> (\exists x p(x)) & q()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val partialVacuousExistsAxiom = derivedAxiom("partial vacuous exists quantifier",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ (p_(x_) & q_()) <-> \\exists x_ p_(x_) & q_()".asFormula)),
      equivR(1) <(
        existsL(-1) & andR(1) <(existsR("x_".asVariable)(1) & prop & done, prop & done),
        andL('L) & existsL(-1) & existsR("x_".asVariable)(1) & prop & done
      )
  )

  /**
    * {{{Axiom "V[:*] vacuous assign nondet".
    *    [x:=*;]p() <-> p()
    * End.
    * @todo reorient
    * @Derived
    * */
  lazy val vacuousBoxAssignNondetAxiom = derivedAxiom("V[:*] vacuous assign nondet",
    Sequent(IndexedSeq(), IndexedSeq("([x_:=*;]p_()) <-> p_()".asFormula)),
    useAt("[:*] assign nondet")(1, 0::Nil) &
      useAt("vacuous all quantifier")(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "V<:*> vacuous assign nondet".
    *    <x:=*;>p() <-> p()
    * End.
    * }}}
    *
    * @todo reorient
    * @Derived
    */
  lazy val vacuousDiamondAssignNondetAxiom = derivedAxiom("V<:*> vacuous assign nondet",
    Sequent(IndexedSeq(), IndexedSeq("(<x_:=*;>p_()) <-> p_()".asFormula)),
    useAt(nondetassigndAxiom.fact)(1, 0::Nil) &
      useAt(vacuousExistsAxiom.fact)(1, 0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "Domain Constraint Conjunction Reordering".
    *    [{c & (H(||) & q(||))}]p(||) <-> [{c & (q(||) & H(||))}]p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val domainCommute = derivedAxiom("Domain Constraint Conjunction Reordering",
    Sequent(IndexedSeq(), IndexedSeq("[{c_ & (H_(||) & q_(||))}]p_(||) <-> [{c_ & (q_(||) & H_(||))}]p_(||)".asFormula)),
    useAt(andCommute.fact)(1, 0::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "[] post weaken".
    *   [a;]p(||)  ->  [a;](q(||)->p(||))
    * End.
    * }}}
    *
    * @Derived from M (or also from K)
    */
  lazy val postconditionWeaken = derivedAxiom("[] post weaken",
    Sequent(IndexedSeq(), IndexedSeq("([a_;]p_(||))  ->  [a_;](q_(||)->p_(||))".asFormula)),
    implyR(1) & monb & prop
  )

  /**
    * {{{Axiom "& commute".
    *    (p() & q()) <-> (q() & p())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val andCommute = derivedAxiom("& commute", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (q_() & p_())".asFormula)), prop)

  /**
    * {{{Axiom "& associative".
    *    ((p() & q()) & r()) <-> (p() & (q() & r()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val andAssoc = derivedAxiom("& associative", Sequent(IndexedSeq(), IndexedSeq("((p_() & q_()) & r_()) <-> (p_() & (q_() & r_()))".asFormula)), prop)

  /**
    * {{{Axiom "& reflexive".
    *    p() & p() <-> p()
    * End.
    * }}}
    */
  lazy val andReflexive = derivedAxiom("& reflexive", Sequent(IndexedSeq(), IndexedSeq("p_() & p_() <-> p_()".asFormula)), prop)

  /**
    * {{{Axiom "<-> true".
    *    (p() <-> true) <-> p()
    * End.
    * }}}
    */
  lazy val equivTrue = derivedAxiom("<-> true", Sequent(IndexedSeq(), IndexedSeq("(p() <-> true) <-> p()".asFormula)), prop)

  /**
    * {{{Axiom "-> self".
    *    (p() -> p()) <-> true
    * End.
    * }}}
    */
  lazy val implySelf = derivedAxiom("-> self", Sequent(IndexedSeq(), IndexedSeq("(p_() -> p_()) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "-> converse".
    *    (p() -> q()) <-> (!q() -> !p())
    * End.
    * }}}
    */
  lazy val converseImply = derivedAxiom("-> converse", Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> (!q_() -> !p_())".asFormula)), prop)

  /**
    * {{{Axiom "!& deMorgan".
    *    (!(p() & q())) <-> ((!p()) | (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notAnd = derivedAxiom("!& deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() & q_())) <-> ((!p_()) | (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!| deMorgan".
    *    (!(p() | q())) <-> ((!p()) & (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notOr = derivedAxiom("!| deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() | q_())) <-> ((!p_()) & (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!-> deMorgan".
    *    (!(p() -> q())) <-> ((p()) & (!q()))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notImply = derivedAxiom("!-> deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() -> q_())) <-> ((p_()) & (!q_()))".asFormula)), prop)

  /**
    * {{{Axiom "!<-> deMorgan".
    *    (!(p() <-> q())) <-> (((p()) & (!q())) | ((!p()) & (q())))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val notEquiv = derivedAxiom("!<-> deMorgan", Sequent(IndexedSeq(), IndexedSeq("(!(p_() <-> q_())) <-> (((p_()) & (!q_())) | ((!p_()) & (q_())))".asFormula)), prop)

  /**
    * {{{Axiom "-> expand".
    *    (p() -> q()) <-> ((!p()) | q())
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val implyExpand = derivedAxiom("-> expand", Sequent(IndexedSeq(), IndexedSeq("(p_() -> q_()) <-> ((!p_()) | q_())".asFormula)), prop)

  /**
    * {{{Axiom "PC1".
    *    p()&q() -> p()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC1
    */
  lazy val PC1 = derivedAxiom("PC1", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> p_()".asFormula)), prop)

  /**
    * {{{Axiom "PC2".
    *    p()&q() -> q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC2
    */
  lazy val PC2 = derivedAxiom("PC2", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> q_()".asFormula)), prop)

  /**
    * {{{Axiom "PC3".
    *    p()&q() -> ((p()->r())->(p()->q()&r())) <-> true
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC3
    */
  lazy val PC3 = derivedAxiom("PC3", Sequent(IndexedSeq(), IndexedSeq("p_()&q_() -> ((p_()->r_())->(p_()->q_()&r_())) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "PC9".
    *    p() -> p() | q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC9
    */
  lazy val PC9 = derivedAxiom("PC9", Sequent(IndexedSeq(), IndexedSeq("p_() -> p_() | q_()".asFormula)), prop)

  /**
    * {{{Axiom "PC10".
    *    q() -> p() | q()
    * End.
    * }}}
    *
    * @Derived
    * @Note implements Cresswell, Hughes. A New Introduction to Modal Logic, PC10
    */
  lazy val PC10 = derivedAxiom("PC10", Sequent(IndexedSeq(), IndexedSeq("q_() -> p_() | q_()".asFormula)), prop)

  /**
    * {{{Axiom "-> tautology".
    *    (p() -> (q() -> p()&q())) <-> true
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val implyTautology = derivedAxiom("-> tautology", Sequent(IndexedSeq(), IndexedSeq("(p_() -> (q_() -> p_()&q_())) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "->' derive imply".
    *    (p(||) -> q(||))' <-> (!p(||) | q(||))'
    * End.
    * }}}
    *
    * @Derived by CE
    */
  lazy val Dimply = derivedAxiom("->' derive imply",
    Sequent(IndexedSeq(), IndexedSeq("(p_(||) -> q_(||))' <-> (!p_(||) | q_(||))'".asFormula)),
    useAt(implyExpand.fact)(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "\forall->\exists".
    *    (\forall x p(x)) -> (\exists x p(x))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val forallThenExistsAxiom = derivedAxiom("\\forall->\\exists",
    Sequent(IndexedSeq(), IndexedSeq("(\\forall x_ p_(x_)) -> (\\exists x_ p_(x_))".asFormula)),
    implyR(1) &
      useAt(existsGeneralize.fact, PosInExpr(1::Nil))(1) &
      useAt("all instantiate")(-1) &
      closeId
  )

  /**
    * {{{Axiom "->true".
    *    (p()->true) <-> true
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val impliesTrue = derivedAxiom("->true", Sequent(IndexedSeq(), IndexedSeq("(p_()->true) <-> true".asFormula)), prop)

  /**
    * {{{Axiom "true->".
    *    (true->p()) <-> p()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val trueImplies = derivedAxiom("true->", Sequent(IndexedSeq(), IndexedSeq("(true->p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{Axiom "&true".
   *    (p()&true) <-> p()
   * End.
   * }}}
    *
    * @Derived
   */
  lazy val andTrue = derivedAxiom("&true", Sequent(IndexedSeq(), IndexedSeq("(p_()&true) <-> p_()".asFormula)), prop)

  /* inverse andtrue axiom for chase */
  lazy val invAndTrue = derivedAxiom("&true inv", Sequent(IndexedSeq(), IndexedSeq("p_() <-> (p_()&true)".asFormula)), prop)

  /**
   * {{{Axiom "true&".
   *    (true&p()) <-> p()
   * End.
   * }}}
    *
    * @Derived
   */
  lazy val trueAnd = derivedAxiom("true&", Sequent(IndexedSeq(), IndexedSeq("(true&p_()) <-> p_()".asFormula)), prop)

  /**
   * {{{Axiom "0*".
   *    (0*f()) = 0
   * End.
   * }}}
    *
    * @Derived
   */
  lazy val zeroTimes = derivedAxiom("0*", Sequent(IndexedSeq(), IndexedSeq("(0*f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0*x = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "*0".
    *    (f()*0) = 0
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val timesZero = derivedAxiom("*0", Sequent(IndexedSeq(), IndexedSeq("(f_()*0) = 0".asFormula)),
    if (false) useAt(timesCommutative.fact)(1, 0::Nil) & byUS(zeroTimes)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x*0 = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
   * {{{Axiom "0+".
   *    (0+f()) = f()
   * End.
   * }}}
    *
    * @Derived
   */
  lazy val zeroPlus = derivedAxiom("0+", Sequent(IndexedSeq(), IndexedSeq("(0+f_()) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0+x = x)".asFormula, TactixLibrary.RCF)))

  /**
    * {{{Axiom "+0".
    *    (f()+0) = f()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val plusZero = derivedAxiom("+0", Sequent(IndexedSeq(), IndexedSeq("(f_()+0) = f_()".asFormula)),
    if (false) useAt(plusCommutative.fact)(1, 0::Nil) & byUS(zeroPlus)
    else allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x+0 = x)".asFormula, TactixLibrary.RCF))
  )

  // differential equations

  /**
    * {{{Axiom "DW differential weakening".
    *    [{c&q(||)}]p(||) <-> ([{c&q(||)}](q(||)->p(||)))
    *    /* [x'=f(x)&q(x);]p(x) <-> ([x'=f(x)&q(x);](q(x)->p(x))) THEORY */
    * End.
    * }}}
    *
    * @see footnote 3 in "Andre Platzer. A uniform substitution calculus for differential dynamic logic. In Amy P. Felty and Aart Middeldorp, editors, International Conference on Automated Deduction, CADE'15, Berlin, Germany, Proceedings, volume 9195 of LNCS, pages 467-481. Springer, 2015. arXiv 1503.01981, 2015."
    */
  lazy val DWeakening = derivedAxiom("DW differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) <-> ([{c_&q_(||)}](q_(||)->p_(||)))".asFormula)),
    equivR(1) <(
      /* equiv left */
      cut("[{c_&q_(||)}](p_(||)->(q_(||)->p_(||)))".asFormula) <(
        /* use */ useAt("K modal modus ponens", PosInExpr(0::Nil))(-2) & implyL(-2) <(close, close),
        /* show */ G(2) & prop
        ),
      /* equiv right */
      useAt("K modal modus ponens", PosInExpr(0::Nil))(-1) & implyL(-1) <(cohide(2) & byUS("DW base"), close)
      )
  )

  /**
    * {{{Axiom "DW differential weakening and".
    *    [{c&q(||)}]p(||) -> ([{c&q(||)}](q(||)&p(||)))
    * End.
    * }}}
    */
  lazy val DWeakeningAnd = derivedAxiom("DW differential weakening and",
    Sequent(IndexedSeq(), IndexedSeq("[{c_&q_(||)}]p_(||) -> ([{c_&q_(||)}](q_(||)&p_(||)))".asFormula)),
    implyR(1) & cut("[{c_&q_(||)}](q_(||)->(p_(||)->(q_(||)&p_(||))))".asFormula) <(
      /* use */ useAt("K modal modus ponens", PosInExpr(0::Nil))('Llast) & implyL('Llast) <(
        cohide('Rlast) & byUS("DW base") & done,
        useAt("K modal modus ponens", PosInExpr(0::Nil))('Llast) & implyL('Llast) <(close, close)),
      /* show */ G('Rlast) & prop
      )
  )

  /**
    * {{{Axiom "DR differential refine".
    *    ([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)
    * End.
    *
    * @Derived
    * }}}
    */
  lazy val DiffRefine = derivedAxiom("DR differential refine",
    Sequent(IndexedSeq(),IndexedSeq("([{c&q(||)}]p(||) <- [{c&r(||)}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) &
      useAt("DMP differential modus ponens", PosInExpr(1::Nil))(1) &
      useAt("DW differential weakening", PosInExpr(1::Nil))(1) & closeId
  )

  /**
    * {{{Axiom "DR<> diamond differential refine".
    *    (<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)
    * End.
    *
    * @Derived
    * }}}
    */
  lazy val DiffRefineDiamond = derivedAxiom("DR<> differential refine",
    Sequent(IndexedSeq(),IndexedSeq("(<{c&q(||)}>p(||) <- <{c&r(||)}>p(||)) <- [{c&r(||)}]q(||)".asFormula)),
    implyR(1) & implyR(1) &
      useAt("<> diamond", PosInExpr(1::Nil))(1) &
      useAt("<> diamond", PosInExpr(1::Nil))(-2) & notL(-2) & notR(1) &
      implyRi()(AntePos(1), SuccPos(0)) & implyRi &
      byUS("DR differential refine")
  )

  /**
    * {{{Axiom "DC differential cut".
    *    ([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)
    * End.
    *
    * @Derived
    * }}}
    */
  lazy val DiffCut = derivedAxiom("DC differential cut",
    Sequent(IndexedSeq(),IndexedSeq("([{c&q(||)}]p(||) <-> [{c&(q(||)&r(||))}]p(||)) <- [{c&q(||)}]r(||)".asFormula)),
    implyR(1) & equivR(1) <
      (
        implyRi()(AntePos(1), SuccPos(0)) &
          useAt("DR differential refine", PosInExpr(1::Nil))(1) &
          useAt("DW differential weakening", PosInExpr(0::Nil))(1) & G(1) & prop ,
        useAt("DW differential weakening and", PosInExpr(0::Nil))(-1) &
          implyRi()(AntePos(1), SuccPos(0)) & implyRi & byUS("DR differential refine"))
  )

  /**
    * {{{Axiom "DI differential invariance".
    *  ([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))
    *  //([x'=f(x)&q(x);]p(x) <-> [?q(x);]p(x)) <- (q(x) -> [x'=f(x)&q(x);]((p(x))')) THEORY
    * End.
    * }}}
    *
    * @Derived
    */
  private lazy val DIinvarianceF = "([{c&q(||)}]p(||) <-> [?q(||);]p(||)) <- (q(||) -> [{c&q(||)}]((p(||))'))".asFormula
  lazy val DIinvariance = DerivedAxiomProvableSig.axioms("DI differential invariance") /*derivedAxiom("DI differential invariance",
    Sequent(IndexedSeq(), IndexedSeq(DIinvarianceF)),
    implyR(1) & equivR(1) <(
      testb(1) &
        useAt("DX differential skip")(-2) &
        close
      ,
      testb(-2) &
        useAt("DI differential invariant")(1) &
        prop & onAll(close)
    )
  )*/

  /**
    * {{{Axiom "DI differential invariant".
    *    [{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))
    *    // [x'=f(x)&q(x);]p(x) <- (q(x) -> (p(x) & [x'=f(x)&q(x);]((p(x))'))) THEORY
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val DIinvariant = derivedAxiom("DI differential invariant",
    Sequent(IndexedSeq(), IndexedSeq("[{c&q(||)}]p(||) <- (q(||)-> (p(||) & [{c&q(||)}]((p(||))')))".asFormula)),
    implyR(1) & useAt(implyDistAndAxiom.fact, PosInExpr(0::Nil))(-1) & andL(-1) &
      useAt("[?] test", PosInExpr(1::Nil))(-1) &
      cut(DIinvarianceF) <(
        prop & onAll(close)
        ,
        cohide(2) & by(DIinvariance)
        )
  )

  /** 15624 */
  lazy val DAIinvariant = derivedAxiom("DAI differential invariant",
    Sequent(IndexedSeq(), IndexedSeq("([\\dexists{x}{c&q(||)}]p(|x|)) <- ((\\forall x (q(||) -> p(|x|))) & [\\dexists{x}{c&q(||)}]((p(|x|))'))".asFormula)),
    implyR(1) & andL(-1) & useAt("[?] test", PosInExpr(1::Nil))(-1, PosInExpr(0::Nil)) &
      cut("([\\dexists{x}{c&q(||)}]p(|x|) <-> \\forall x [?q(||);]p(|x|)) <- [\\dexists{x}{c&q(||)}](p(|x|)')".asFormula)
        <(
        prop & onAll(close),
        cohide(2) & useAt("DAI differential invariance", PosInExpr(Nil))(1, PosInExpr(Nil))
      )
  )

  /**
    * {{{Axiom "DIo open differential invariance <".
    *    ([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val DIOpeninvariantLess = derivedAxiom("DIo open differential invariance <",
    Sequent(IndexedSeq(), IndexedSeq("([{c&q(||)}]f(||)<g(||) <-> [?q(||);]f(||)<g(||)) <- (q(||) -> [{c&q(||)}](f(||)<g(||) -> (f(||)<g(||))'))".asFormula)),
    useAt(flipLess.fact)(1, 1::0::1::Nil) &
      useAt(flipLess.fact)(1, 1::1::1::Nil) &
      useAt(flipLess.fact)(1, 0::1::1::0::Nil) &
      HilbertCalculus.Derive.Dless(1, 0::1::1::1::Nil) &
      useAt(flipLessEqual.fact)(1, 0::1::1::1::Nil) &
      useExpansionAt(">' derive >")(1, 0::1::1::1::Nil) &
      byUS("DIo open differential invariance >")
  )

  /**
    * {{{Axiom "DV differential variant <=".
    *    <{c&true}>f(||)<=g(||) <- \exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val DVLessEqual = derivedAxiom("DV differential variant <=",
    Sequent(IndexedSeq(), IndexedSeq("<{c&true}>f(||)<=g(||) <- \\exists e_ (e_>0 & [{c&true}](f(||)>=g(||) -> f(||)'<=g(||)'-e_))".asFormula)),
    useAt(flipLessEqual.fact)(1, 1::1::Nil) &
      useAt(flipGreaterEqual.fact)(1, 0::0::1::1:: 0::Nil) &
      useAt(flipLessEqual.fact)(1, 0::0::1::1:: 1::Nil) &
      // transform g(||)'+e_<=f(||)' to g(||)'<=f(||)'-e_
      useAt(TactixLibrary.proveBy("s()-r()>=t() <-> s()>=t()+r()".asFormula, QE & done), PosInExpr(0::Nil))(1, 0::0::1::1:: 1::Nil) &
      byUS("DV differential variant >=")
  )

  /**
    * {{{Axiom "DX diamond differential skip".
    *    <{c&q(||)}>p(||) <- q(||)&p(||)
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val Dskipd = derivedAxiom("DX diamond differential skip",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q(||)}>p(||) <- q(||)&p(||)".asFormula)),
    useAt(doubleNegationAxiom.fact, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt(notAnd.fact)(1, 0::0::Nil) &
      useAt(implyExpand.fact, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt("DX differential skip", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt("<> diamond")(1, 0::Nil) & implyR(1) & close
  )

  /**
    * {{{Axiom "DS differential equation solution".
    *    [{x'=c()}]p(x) <-> \forall t (t>=0 -> [x:=x+(c()*t);]p(x))
    * End.
    * }}}
    *
    * @Derived
    * @TODO postcondition formulation is weaker than that of DS&
    */
  lazy val DSnodomain = derivedAxiom("DS differential equation solution",
    Sequent(IndexedSeq(), IndexedSeq("[{x_'=c_()}]p_(x_) <-> \\forall t_ (t_>=0 -> [x_:=x_+(c_()*t_);]p_(x_))".asFormula)),
    useAt("DS& differential equation solution")(1, 0::Nil) &
      useAt(impliesTrue.fact)(1, 0::0::1::0::0::Nil) &
      useAt("vacuous all quantifier")(1, 0::0::1::0::Nil) &
      useAt(trueImplies.fact)(1, 0::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "Dsol differential equation solution".
    *    <{x'=c()}>p(x) <-> \exists t (t>=0 & <x:=x+(c()*t);>p(x))
    * End.
    * }}}
    *
    * @Derived
    * @TODO postcondition formulation is weaker than that of DS&
    */
  lazy val DSdnodomain = derivedAxiom("Dsol differential equation solution",
    Sequent(IndexedSeq(), IndexedSeq("<{x_'=c_()}>p_(x_) <-> \\exists t_ (t_>=0 & <x_:=x_+(c_()*t_);>p_(x_))".asFormula)),
    useAt(DSddomain.fact)(1, 0::Nil) &
      useAt(impliesTrue.fact)(1, 0::0::1::0::0::Nil) &
      useAt("vacuous all quantifier")(1, 0::0::1::0::Nil) &
      useAt(trueAnd.fact)(1, 0::0::1::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "Dsol& differential equation solution".
    *    <{x'=c()&q(x)}>p(||) <-> \exists t (t>=0 & ((\forall s ((0<=s&s<=t) -> q(x+(c()*s)))) & <x:=x+(c()*t);>p(||)))
    * End.
    * }}}
    */
  lazy val DSddomain = derivedAxiom("Dsol& differential equation solution",
    Sequent(IndexedSeq(), IndexedSeq("<{x_'=c()&q(x_)}>p(|x_'|) <-> \\exists t_ (t_>=0 & ((\\forall s_ ((0<=s_&s_<=t_) -> q(x_+(c()*s_)))) & <x_:=x_+(c()*t_);>p(|x_'|)))".asFormula)),
    useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DS& differential equation solution")(1, 0::0::Nil) &
      useAt("all dual time", PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt("!! double negation")(1, 0::Nil) &
      useAt(notImply.fact)(1, 0::0::Nil) &
      useAt(notImply.fact)(1, 0::0::1::Nil) &
      useAt("<> diamond")(1, 0::0::1::1::Nil) &
      //useAt("& associative", PosInExpr(1::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  //  lazy val existsDualAxiom: LookupLemma = derivedAxiom("exists dual",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq("\\exists x q(x) <-> !(\\forall x (!q(x)))".asFormula)))
  //      (CutRight("\\exists x q(x) <-> !!(\\exists x (!!q(x)))".asFormula, SuccPos(0)), 0)
  //      // right branch
  //      (EquivifyRight(SuccPos(0)), 1)
  //      (AxiomaticRule("CE congruence", USubst(
  //        SubstitutionPair(PredicationalOf(context, DotFormula), "\\exists x q(x) <-> !⎵".asFormula) ::
  //          SubstitutionPair(pany, "!\\exists x !!q(x)".asFormula) ::
  //          SubstitutionPair(qany, "\\forall x !q(x)".asFormula) :: Nil
  //      )), 1)
  //      (CommuteEquivRight(SuccPos(0)), 1)
  //      (Axiom("all dual"), 1)
  //      (Close(AntePos(0),SuccPos(0)), 1)
  //  )


  /**
    * {{{Axiom "DG differential pre-ghost".
    *    [{c{|y_|}&q(|y_|)}]p(|y_|) <-> \exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)
    *    // [x'=f(x)&q(x);]p(x) <-> \exists y [{y'=(a(x)*y)+b(x), x'=f(x))&q(x)}]p(x) THEORY
    * End.
    * }}}
    * Pre Differential Auxiliary / Differential Ghost -- not strictly necessary but saves a lot of reordering work.
    */
  lazy val DGpreghost = derivedAxiom("DG differential pre-ghost",
    Sequent(IndexedSeq(), IndexedSeq("[{c{|y_|}&q(|y_|)}]p(|y_|) <-> \\exists y_ [{y_'=(a(|y_|)*y_)+b(|y_|),c{|y_|}&q(|y_|)}]p(|y_|)".asFormula)),
    useAt("DG differential ghost")(1, 0::Nil) &
      useAt(", commute")(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  // diamond differential axioms

  /**
    * {{{Axiom "DGd diamond differential ghost".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)
    *    // <x'=f(x)&q(x);>p(x) <-> \forall y <{x'=f(x),y'=(a(x)*y)+b(x))&q(x)}>p(x) THEORY
    * End.
    * }}}
    */
  lazy val DGddifferentialghost = derivedAxiom("DGd diamond differential ghost",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=(a(|y_|)*y_)+b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DG differential ghost")(1, 0::0::Nil) &
      useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("all dual y", PosInExpr(0::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )


  /**
    * {{{Axiom "DGd diamond inverse differential ghost implicational".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|)  ->  \exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)
    * End.
    * }}}
    */
  lazy val DGdinversedifferentialghostimplicational = derivedAxiom("DGd diamond inverse differential ghost implicational",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|)  <-  \\exists y_ <{y_'=a(||),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::1::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::0::Nil) &
      useAt(doubleNegationAxiom, PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("all dual y")(1, 0::0::Nil) &
      useAt(boxAxiom)(1, 0::0::0::Nil) &
      useAt(converseImply, PosInExpr(1::Nil))(1) &
      byUS("DG inverse differential ghost implicational")
  )

  /**
    * {{{Axiom "DGCd diamond differential ghost const".
    *    <{c{|y_|}&q(|y_|)}>p(|y_|) <-> \forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)
    * End.
    * }}}
    */
  lazy val DGCddifferentialghostconst = derivedAxiom("DGd diamond differential ghost constant",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DG differential ghost constant")(1, 0::0::Nil) &
      useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("all dual y", PosInExpr(0::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val DGCddifferentialghostconstconv = derivedAxiom("DGd diamond differential ghost constant converse",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\forall y_ <{y_'=b(|y_|),c{|y_|}&q(|y_|)}>p(|y_|)".asFormula)),
      useAt(proveBy("<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula, useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
        useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
        useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
        byUS(", commute")))(1,PosInExpr(1::0::Nil)) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("DG differential ghost constant")(1, 0::0::Nil) &
      useAt("!! double negation", PosInExpr(1::Nil))(1, 0::0::0::Nil) &
      useAt("all dual y", PosInExpr(0::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(0::Nil))(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  lazy val DGCddifferentialghostconstexists = derivedAxiom("DGd diamond differential ghost constant exists",
    Sequent(IndexedSeq(), IndexedSeq("<{c{|y_|}&q(|y_|)}>p(|y_|) <-> \\exists y_ <{c{|y_|},y_'=b(|y_|)&q(|y_|)}>p(|y_|)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("DG differential ghost constant all")(1, 0::0::Nil) &
      useAt("!! double negation", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt("all dual y", PosInExpr(0::Nil))(1, 1::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "DWd diamond differential weakening".
    *    <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))
    * End.
    * }}}
    */
  lazy val DWddifferentialweakening = derivedAxiom("DWd diamond differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)&p_(||))".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(proveBy("!(p_() & q_()) <-> (p_() -> !q_())".asFormula, TactixLibrary.prop))(1, 1::0::1::Nil) &
      useAt("DW differential weakening", PosInExpr(1::Nil))(1, 1::0::Nil) &
      byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "DWd2 diamond differential weakening".
    *    <{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))
    * End.
    * }}}
    */
  lazy val DWd2differentialweakening = derivedAxiom("DWd2 diamond differential weakening",
    Sequent(IndexedSeq(), IndexedSeq("<{c&q_(||)}>p_(||) <-> <{c&q_(||)}>(q_(||)->p_(||))".asFormula)),
      equivR(1) <(
        implyRi & CMon(PosInExpr(1::Nil)) & prop & done,
        cutAt("q_(||) & (q_(||)->p_(||))".asFormula)(1, 1::Nil) <(
          implyRi & useAt(Kd2Axiom, PosInExpr(1::Nil))(1) & byUS("DW base")
          ,
          cohideR(1) & CMon(PosInExpr(1::Nil)) & prop & done
          )
        )
  )

  /**
    * {{{Axiom "DCd diamond differential cut".
    *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
    *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
    * End.
    * }}}
    */
  lazy val DCddifferentialcut = derivedAxiom("DCd diamond differential cut",
    Sequent(IndexedSeq(), IndexedSeq("(<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::1::Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1, 1::Nil) &
      byUS("DC differential cut")
  )

  /**
    * {{{Axiom "DCd diamond differential cut".
    *   (<{c&q(||)}>p(||) <-> <{c&(q(||)&r(||))}>p(||)) <- [{c&q(||)}]r(||)
    *   // (<x'=f(x)&q(x); >p(x) <-> <x'=f(x)&(q(x)&r(x));>p(x)) <- [x'=f(x)&q(x);]r(x) THEORY
    * End.
    * }}}
    */
  lazy val commaCommuted = derivedAxiom(",d commute",
    Sequent(IndexedSeq(), IndexedSeq("<{c,d&q(||)}>p(||) <-> <{d,c&q(||)}>p(||)".asFormula)),
      useAt("<> diamond", PosInExpr(1::Nil))(1, 0::Nil) &
      useAt("<> diamond", PosInExpr(1::Nil))(1, 1::Nil) &
      useAt(proveBy("(!p() <-> !q()) <-> (p() <-> q())".asFormula, TactixLibrary.prop))(1) &
      byUS(", commute")
  )

  /**
    * {{{
    *   Axiom "[d] dual".
    *    [{a;}^@]p(||) <-> ![a;]!p(||)
    *   End.
    * }}}
    * @derived
    */
  lazy val dualbAxiom = derivedAxiom("[d] dual",
    Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> ![a;]!p(||)".asFormula)),
    useExpansionAt("[] box")(1, 0::Nil) &
      useAt("<d> dual")(1, 0::0::Nil) &
      useAt("[] box")(1, 0::0::Nil) &
      byUS(equivReflexiveAxiom)
  )
  /**
    * {{{
    *   Axiom "[d] dual direct".
    *    [{a;}^@]p(||) <-> <a;>p(||)
    *   End.
    * }}}
    * @derived
    */
  lazy val dualbDirectAxiom = derivedAxiom("[d] dual direct",
    Sequent(IndexedSeq(), IndexedSeq("[{a;}^@]p(||) <-> <a;>p(||)".asFormula)),
    useExpansionAt("<> diamond")(1, 1::Nil) &
      byUS(dualbAxiom.fact)
  )

  /**
    * {{{
    *   Axiom "<d> dual direct".
    *    <{a;}^@>p(||) <-> [a;]p(||)
    *   End.
    * }}}
    * @derived
    */
  lazy val dualdDirectAxiom = derivedAxiom("<d> dual direct",
    Sequent(IndexedSeq(), IndexedSeq("<{a;}^@>p(||) <-> [a;]p(||)".asFormula)),
    useExpansionAt("[] box")(1, 1::Nil) &
      byUS("<d> dual")
  )

  // differentials

  /**
    * {{{Axiom "x' derive var commuted".
    *    (x_') = (x_)'
    * End.
    * }}}
    */
  lazy val DvariableCommuted = derivedAxiom("x' derive var commuted",
    Sequent(IndexedSeq(), IndexedSeq("(x_') = (x_)'".asFormula)),
    useAt(equalCommute.fact)(1) &
      byUS("x' derive var")
  )

  /**
    * {{{Axiom "x' derive variable".
    *    \forall x_ ((x_)' = x_')
    * End.
    * }}}
    */
  lazy val Dvariable = derivedAxiom("x' derive variable",
    DerivedAxiomProvableSig.startProof(Sequent(IndexedSeq(), IndexedSeq("\\forall x_ ((x_)' = x_')".asFormula)))
    (Skolemize(SuccPos(0)), 0)
    (DerivedAxiomProvableSig.axioms("x' derive var"), 0)
  )
  //  /**
  //   * {{{Axiom "x' derive var".
  //   *    (x_)' = x_'
  //   * End.
  //   * }}}
  //   * @todo derive
  //   */
  //  lazy val DvarF = "((x_)' = x_')".asFormula
  //  lazy val Dvar = derivedAxiom("'x derive var",
  //    Provable.startProof(Sequent(IndexedSeq(), IndexedSeq(DvarF)))
  //      (CutRight("\\forall x_ ((x_)' = x_')".asFormula, SuccPos(0)), 0)
  //      // right branch
  //      (UniformSubstitutionRule.UniformSubstitutionRuleForward(Axiom.axiom("all eliminate"),
  //        USubst(SubstitutionPair(PredOf(Function("p_",None,Real,Bool),Anything), DvarF)::Nil)), 0)
  //      // left branch
  //      (Axiom.axiom("x' derive variable"), 0)
  //    /*TacticLibrary.instantiateQuanT(Variable("x_",None,Real), Variable("x",None,Real))(1) &
  //      byUS("= reflexive")*/
  //  )
  //  lazy val DvarT = TactixLibrary.byUS(Dvar)
  /**
    * {{{Axiom "' linear".
    *    (c()*f(||))' = c()*(f(||))'
    * End.
    * }}}
    */
  lazy val Dlinear = derivedAxiom("' linear",
    Sequent(IndexedSeq(), IndexedSeq("(c_()*f_(||))' = c_()*(f_(||))'".asFormula)),
    useAt("*' derive product")(1, 0::Nil) &
      useAt("c()' derive constant fn")(1, 0::0::0::Nil) &
      useAt(zeroTimes.fact)(1, 0::0::Nil) &
      useAt(zeroPlus.fact)(1, 0::Nil) &
      byUS(equalReflex)
  )

  /**
    * {{{Axiom "' linear right".
    *    (f(||)*c())' = f(||)'*c()
    * End.
    * }}}
    */
  lazy val DlinearRight = derivedAxiom("' linear right",
    Sequent(IndexedSeq(), IndexedSeq("(f(||)*c())' = (f(||))'*c()".asFormula)),
    useAt("*' derive product")(1, 0:: Nil) &
      useAt("c()' derive constant fn")(1, 0:: 1::1::Nil) &
      useAt(timesZero.fact)(1, 0:: 1::Nil) &
      useAt(plusZero.fact)(1, 0:: Nil) &
      byUS(equalReflex)
  )
  //@note elegant proof that clashes for some reason
  //  derivedAxiom("' linear right",
  //  Sequent(IndexedSeq(), IndexedSeq(DlinearRightF)),
  //  useAt("* commute")(1, 0::0::Nil) &
  //    useAt("* commute")(1, 1::Nil) &
  //    by(Dlinear)
  //)


  // real arithmetic

  /**
   * {{{Axiom "= reflexive".
   *    s() = s()
   * End.
   * }}}
   */
  lazy val equalReflex = derivedAxiom("= reflexive", Sequent(IndexedSeq(), IndexedSeq("s_() = s_()".asFormula)),
    allInstantiateInverse(("s_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x x=x".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "= commute".
    *   (f()=g()) <-> (g()=f())
    * End.
    * }}}
    */
  lazy val equalCommute = derivedAxiom("= commute", Sequent(IndexedSeq(), IndexedSeq("(f_()=g_()) <-> (g_()=f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x=y <-> y=x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">= reflexive".
    *    s() >= s()
    * End.
    * }}}
    */
  lazy val greaterEqualReflex = derivedAxiom(">= reflexive", Sequent(IndexedSeq(), IndexedSeq("s_() >= s_()".asFormula)), QE & done)

  /**
    * {{{Axiom "* commute".
    *   (f()*g()) = (g()*f())
    * End.
    * }}}
    */
  lazy val timesCommute = derivedAxiom("* commute", Sequent(IndexedSeq(), IndexedSeq("(f_()*g_()) = (g_()*f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x*y = y*x)".asFormula, TactixLibrary.RCF & done))
  )

  /**
    * {{{Axiom "<=".
    *   (f()<=g()) <-> ((f()<g()) | (f()=g()))
    * End.
    * }}}
    */
  lazy val lessEqual = derivedAxiom("<=", Sequent(IndexedSeq(), IndexedSeq("(f_()<=g_()) <-> ((f_()<g_()) | (f_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x<=y <-> (x<y | x=y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! !=".
    *   (!(f() != g())) <-> (f() = g())
    * End.
    * }}}
    */
  lazy val notNotEqual = derivedAxiom("! !=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() != g_())) <-> (f_() = g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x != y)) <-> (x = y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! =".
    *   !(f() = g()) <-> f() != g()
    * End.
    * }}}
    */
  lazy val notEqual = derivedAxiom("! =", Sequent(IndexedSeq(), IndexedSeq("(!(f_() = g_())) <-> (f_() != g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x = y)) <-> (x != y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! >".
    *   (!(f() > g())) <-> (f() <= g())
    * End.
    * }}}
    */
  lazy val notGreater = derivedAxiom("! >", Sequent(IndexedSeq(), IndexedSeq("(!(f_() > g_())) <-> (f_() <= g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x > y)) <-> (x <= y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "> flip".
    *   (f() > g()) <-> (g() < f())
    * End.
    * */
  lazy val flipGreater = derivedAxiom("> flip", Sequent(IndexedSeq(), IndexedSeq("(f_() > g_()) <-> (g_() < f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x > y) <-> (y < x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">= flip".
    *   (f() >= g()) <-> (g() <= f())
    * End.
    * }}}
    */
  lazy val flipGreaterEqual = derivedAxiom(">= flip", Sequent(IndexedSeq(), IndexedSeq("(f_() >= g_()) <-> (g_() <= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x >= y) <-> (y <= x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "< flip".
    *   (f() < g()) <-> (g() > f())
    * End.
    * */
  lazy val flipLess = derivedAxiom("< flip", Sequent(IndexedSeq(), IndexedSeq("(f_() < g_()) <-> (g_() > f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x < y) <-> (y > x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<= flip".
    *   (f() <= g()) <-> (g() >= f())
    * End.
    * }}}
    */
  lazy val flipLessEqual = derivedAxiom("<= flip", Sequent(IndexedSeq(), IndexedSeq("(f_() <= g_()) <-> (g_() >= f_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((x <= y) <-> (y >= x))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "! <".
    *   (!(f() < g())) <-> (f() >= g())
    * End.
    * }}}
    */
  lazy val notLess = derivedAxiom("! <", Sequent(IndexedSeq(), IndexedSeq("(!(f_() < g_())) <-> (f_() >= g_())".asFormula)),
    useAt(flipGreater.fact, PosInExpr(1::Nil))(1, 0::0::Nil) & useAt(notGreater.fact)(1, 0::Nil) & useAt(flipGreaterEqual.fact)(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "! <=".
    *   (!(f() <= g())) <-> (f() > g())
    * End.
    * }}}
    */
  lazy val notLessEqual = derivedAxiom("! <=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() <= g_())) <-> (f_() > g_())".asFormula)),
    useAt(flipGreaterEqual.fact, PosInExpr(1::Nil))(1, 0::0::Nil) & useAt(notGreaterEqual.fact)(1, 0::Nil) & useAt(flipGreater.fact)(1, 1::Nil) & byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "! >=".
    *   (!(f() >= g())) <-> (f() < g())
    * End.
    * }}}
    */
  lazy val notGreaterEqual = derivedAxiom("! >=", Sequent(IndexedSeq(), IndexedSeq("(!(f_() >= g_())) <-> (f_() < g_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((!(x >= y)) <-> (x < y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ associative".
    *    (f()+g()) + h() = f() + (g()+h())
    * End.
    * }}}
    */
  lazy val plusAssociative = derivedAxiom("+ associative", Sequent(IndexedSeq(), IndexedSeq("(f_() + g_()) + h_() = f_() + (g_() + h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((x + y) + z = x + (y + z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* associative".
    *    (f()*g()) * h() = f() * (g()*h())
    * End.
    * }}}
    */
  lazy val timesAssociative = derivedAxiom("* associative", Sequent(IndexedSeq(), IndexedSeq("(f_() * g_()) * h_() = f_() * (g_() * h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((x * y) * z = x * (y * z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ commute".
    *    f()+g() = g()+f()
    * End.
    * }}}
    */
  lazy val plusCommutative = derivedAxiom("+ commute", Sequent(IndexedSeq(), IndexedSeq("f_()+g_() = g_()+f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x+y = y+x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* commute".
    *    f()*g() = g()*f()
    * End.
    * }}}
    */
  lazy val timesCommutative = derivedAxiom("* commute", Sequent(IndexedSeq(), IndexedSeq("f_()*g_() = g_()*f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x*y = y*x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "distributive".
    *    f()*(g()+h()) = f()*g() + f()*h()
    * End.
    * }}}
    */
  lazy val distributive = derivedAxiom("distributive", Sequent(IndexedSeq(), IndexedSeq("f_()*(g_()+h_()) = f_()*g_() + f_()*h_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x (x*(y+z) = x*y + x*z)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ identity".
    *    f()+0 = f()
    * End.
    * }}}
    */
  lazy val plusIdentity = zeroPlus

  /**
    * {{{Axiom "* identity".
    *    f()*1 = f()
    * End.
    * }}}
    */
  lazy val timesIdentity = derivedAxiom("* identity", Sequent(IndexedSeq(), IndexedSeq("f_()*1 = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x*1 = x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ inverse".
    *    f() + (-f()) = 0
    * End.
    * }}}
    */
  lazy val plusInverse = derivedAxiom("+ inverse", Sequent(IndexedSeq(), IndexedSeq("f_() + (-f_()) = 0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x + (-x) = 0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* inverse".
    *    f() != 0 -> f()*(f()^-1) = 1
    * End.
    * }}}
    */
  lazy val timesInverse = derivedAxiom("* inverse", Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> f_()*(f_()^-1) = 1".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x != 0 -> x*(x^-1) = 1)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "positivity".
    *    f() < 0 | f() = 0 | 0 < f()
    * End.
    * }}}
    */
  lazy val positivity = derivedAxiom("positivity", Sequent(IndexedSeq(), IndexedSeq("f_() < 0 | f_() = 0 | 0 < f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x < 0 | x = 0 | 0 < x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+ closed".
    *    0 < f() & 0 < g() -> 0 < f()+g()
    * End.
    * }}}
    */
  lazy val plusClosed = derivedAxiom("+ closed", Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()+g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x+y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "* closed".
    *    0 < f() & 0 < g() -> 0 < f()*g()
    * End.
    * }}}
    */
  lazy val timesClosed = derivedAxiom("* closed", Sequent(IndexedSeq(), IndexedSeq("0 < f_() & 0 < g_() -> 0 < f_()*g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (0 < x & 0 < y -> 0 < x*y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<".
    *    f() < g() <-> 0 < g()-f()
    * End.
    * }}}
    */
  lazy val less = derivedAxiom("<", Sequent(IndexedSeq(), IndexedSeq("f_() < g_() <-> 0 < g_()-f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x < y <-> 0 < y-x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">".
    *    f() > g() <-> g() < f()
    * End.
    * }}}
    */
  lazy val greater = derivedAxiom(">", Sequent(IndexedSeq(), IndexedSeq("f_() > g_() <-> g_() < f_()".asFormula)), byUS(flipGreater))

  // built-in arithmetic

  /**
    * {{{Axiom "!= elimination".
    *   f()!=g() <-> \exists z (f()-g())*z=1
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val notEqualElim = derivedAxiom("!= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()!=g_()) <-> \\exists z_ ((f_()-g_())*z_=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x!=y) <-> \\exists z_ ((x-y)*z_=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom ">= elimination".
    *   f()>=g() <-> \exists z f()-g()=z^2
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterEqualElim = derivedAxiom(">= elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>=g_()) <-> \\exists z_ (f_()-g_()=z_^2)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>=y) <-> \\exists z_ (x-y=z_^2))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "> elimination".
    *   f()>g() <-> \exists z (f()-g())*z^2=1
    * End.
    * }}}
    * @see André Platzer, Jan-David Quesel, and Philipp Rümmer. Real world verification. CADE 2009.
    */
  //@note disabled since not provable with Z3; intended to replace QE with core implementation
//  lazy val greaterElim = derivedAxiom("> elimination", Sequent(IndexedSeq(), IndexedSeq("(f_()>g_()) <-> \\exists z_ ((f_()-g_())*z_^2=1)".asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
//    byUS(proveBy("\\forall y \\forall x ((x>y) <-> \\exists z_ ((x-y)*z_^2=1))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "1>0".
    *   1>0
    * End.
    * }}}
    */
  lazy val oneGreaterZero = derivedAxiom("1>0", Sequent(IndexedSeq(), IndexedSeq("1>0".asFormula)), TactixLibrary.RCF)

  /**
    * {{{Axiom "nonnegative squares".
    *   f()^2>=0
    * End.
    * }}}
    */
  lazy val nonnegativeSquares = derivedAxiom("nonnegative squares", Sequent(IndexedSeq(), IndexedSeq("f_()^2>=0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
    byUS(proveBy("\\forall x (x^2>=0)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom ">2!=".
    *   f()>g() -> f()!=g()
    * End.
    * }}}
    */
  lazy val greaterImpliesNotEqual = derivedAxiom(">2!=", Sequent(IndexedSeq(), IndexedSeq("f_()>g_() -> f_()!=g_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x (x>y -> x!=y)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "> monotone".
    *   f()+h()>g() <- f()>g() & h()>=0
    * End.
    * }}}
    */
  lazy val greaterMonotone = derivedAxiom("> monotone", Sequent(IndexedSeq(), IndexedSeq("f_()+h_()>g_() <- f_()>g_() & h_()>=0".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x (x+z>y <- x>y & z>=0)".asFormula, TactixLibrary.RCF))
  )

  // stuff

  /**
    * {{{Axiom "abs".
    *   (abs(s()) = t()) <->  ((s()>=0 & t()=s()) | (s()<0 & t()=-s()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
    */
  lazy val absDef = derivedAxiom("abs", Sequent(IndexedSeq(), IndexedSeq("(abs(s_()) = t_()) <->  ((s_()>=0 & t_()=s_()) | (s_()<0 & t_()=-s_()))".asFormula)),
    allInstantiateInverse(("s_()".asTerm, "x".asVariable), ("t_()".asTerm, "y".asVariable))(1) &
    byUS(proveBy("\\forall y \\forall x ((abs(x) = y) <->  ((x>=0 & y=x) | (x<0 & y=-x)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "min".
    *    (min(f(), g()) = h()) <-> ((f()<=g() & h()=f()) | (f()>g() & h()=g()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
    */
  lazy val minDef = derivedAxiom("min", Sequent(IndexedSeq(), IndexedSeq("(min(f_(), g_()) = h_()) <-> ((f_()<=g_() & h_()=f_()) | (f_()>g_() & h_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((min(x, y) = z) <-> ((x<=y & z=x) | (x>y & z=y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "max".
    *    (max(f(), g()) = h()) <-> ((f()>=g() & h()=f()) | (f()<g() & h()=g()))
    * End.
    * }}}
    *
    * @Derived from built-in arithmetic abs in [[edu.cmu.cs.ls.keymaerax.tools.Mathematica]]
    */
  lazy val maxDef = derivedAxiom("max", Sequent(IndexedSeq(), IndexedSeq("(max(f_(), g_()) = h_()) <-> ((f_()>=g_() & h_()=f_()) | (f_()<g_() & h_()=g_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable))(1) &
    byUS(proveBy("\\forall z \\forall y \\forall x ((max(x, y) = z) <-> ((x>=y & z=x) | (x<y & z=y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<*> stuck".
    *    <{a;}*>p(||) <-> <{a;}*>p(||)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  lazy val loopStuck = derivedAxiom("<*> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<{a_;}*>p_(||) <-> <{a_;}*>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  lazy val programStuck = derivedAxiom("<a> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<a_;>p_(||) <-> <a_;>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "<'> stuck".
    *    <{c&q(||)}>p(||) <-> <{c&q(||)}>p(||)
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  lazy val odeStuck = derivedAxiom("<'> stuck",
    Sequent(IndexedSeq(), IndexedSeq("<{c_&q_(||)}>p_(||) <-> <{c_&q_(||)}>p_(||)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "& recursor".
    *    p() & q() <-> p() & q()
    * End.
    * }}}
    *
    */
  lazy val andRecursor = derivedAxiom("& recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() & q_()) <-> (p_() & q_())".asFormula)), prop)

  /**
    * {{{Axiom "| recursor".
    *    p() | q() <-> p() | q()
    * End.
    * }}}
    *
    */
  lazy val orRecursor = derivedAxiom("| recursor", Sequent(IndexedSeq(), IndexedSeq("(p_() | q_()) <-> (p_() | q_())".asFormula)), prop)

  /**
    * {{{Axiom "<= both".
    *    f()<=g() <- ((f() <= F() & gg() <= g()) & F() <= gg())
    * End.
    * }}}
    */

  lazy val intervalLEBoth = derivedAxiom("<= both", Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() <= gg_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall X \\forall y \\forall x (x<=y <- ((x<=X & yy<=y) & X<=yy))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "< both".
    *    f()<g() <- ((f() <= F() & gg() <= g()) & F() < gg())
    * End.
    * }}}
    */

  lazy val intervalLBoth = derivedAxiom("< both", Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <- ((f_()<=F_() & gg_()<=g_()) & F_() < gg_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall X \\forall y \\forall x (x<y <- ((x<=X & yy<=y) & X<yy))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "neg<= up".
    *    -f()<=h() <- (ff()<=f() & -ff() <= h())
    * End.
    * }}}
    */

  lazy val intervalUpNeg = derivedAxiom("neg<= up", Sequent(IndexedSeq(), IndexedSeq("-f_()<=h_() <- (ff_() <= f_() & -ff_() <= h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall z \\forall x (-x<=z <- (xx<=x & -xx <=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "abs<= up".
    *    abs(f())<=h() <- ((ff()<=f() & f() <= F()) & (-ff()<=h() & F()<=h()))
    * End.
    * }}}
    */

  lazy val intervalUpAbs = derivedAxiom("abs<= up", Sequent(IndexedSeq(), IndexedSeq("abs(f_())<=h_() <- ((ff_() <= f_() & f_() <= F_()) & (-ff_() <= h_() & F_()<= h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable),("F_()".asTerm,"X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall xx \\forall z \\forall x (abs(x)<=z <- ((xx<=x & x <=X) & (-xx <= z & X <= z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "max<= up".
    *    max(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F() <= h() & G()<=h()))
    * End.
    * }}}
    */
  lazy val intervalUpMax = derivedAxiom("max<= up", Sequent(IndexedSeq(), IndexedSeq("max(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() & G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (max(x,y)<=z <- ((x<=X & y<=Y) & (X<=z & Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "min<= up".
    *    min(f(),g())<=h() <- ((f()<=F() & g()<=G()) & (F()<=h() | G()<=h()))
    * End.
    * }}}
    */
  lazy val intervalUpMin = derivedAxiom("min<= up", Sequent(IndexedSeq(), IndexedSeq("min(f_(),g_())<=h_() <- ((f_()<=F_() & g_()<=G_()) & (F_() <= h_() | G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (min(x,y)<=z <- ((x<=X & y<=Y) & (X<=z | Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "+<= up".
    *    f()+g()<=h() <- ((f()<=F() & g()<=G()) & F()+G()<=h())
    * End.
    * }}}
    */
  lazy val intervalUpPlus = derivedAxiom("+<= up", Sequent(IndexedSeq(), IndexedSeq("f_()+g_()<=h_() <- ((f_()<=F_() & g_()<=G_()) & F_()+G_()<=h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall X \\forall z \\forall y \\forall x (x+y<=z <- ((x<=X & y<=Y) & X+Y<=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "-<= up".
    *    f()-g()<=h() <- ((f()<=F() & gg()<=g()) & F()-gg()<=h())
    * End.
    * }}}
    */
  lazy val intervalUpMinus = derivedAxiom("-<= up", Sequent(IndexedSeq(), IndexedSeq("f_()-g_()<=h_() <- ((f_()<=F_() & gg_()<=g_()) & F_()-gg_()<=h_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall X \\forall z \\forall y \\forall x (x-y<=z <- ((x<=X & yy<=y) & X-yy<=z))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "*<= up".
    *    f()*g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & (ff()*gg()<=h() & ff()*G()<=h() & F()*gg()<=h() & F()*G()<=h()))
    * End.
    * }}}
    */
  // A more efficient check is available if we know that f_() or g_() is strictly positive
  // For example, if 0<= ff_(), then we only need ff_() * G_() <= h_() & F_() * G() <= h_()

  lazy val intervalUpTimes = derivedAxiom("*<= up", Sequent(IndexedSeq(), IndexedSeq("f_()*g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (ff_()*gg_()<=h_() & ff_()*G_()<=h_() & F_()*gg_()<=h_() & F_()*G_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x*y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (xx*yy<=z & xx*Y<=z & X*yy<=z & X*Y<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "1Div<= up".
    *    1/f()<=h() <- ((ff()<=f() & ff()*f()>0) & (1/ff()<=h()))
    * End.
    * }}}
    */
  lazy val intervalUp1Divide = derivedAxiom("1Div<= up", Sequent(IndexedSeq(), IndexedSeq("1/f_()<=h_() <- ((F_()<=f_() & F_()*f_()>0) & (1/F_()<=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall y \\forall x (1/x<=y <- ((X<=x & X*x>0) & (1/X<=y)))".asFormula, TactixLibrary.RCF))
  )
  /**
    * {{{Axiom "Div<= up".
    *    f()/g()<=h() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0<gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
    * End.
    * }}}
    */
  // A more efficient check is available

//  lazy val intervalUpDivide = derivedAxiom("Div<= up", Sequent(IndexedSeq(), IndexedSeq(("f_()/g_()<=h_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0<gg_()) & (ff_()/gg_()<=h_() & ff_()/G_()<=h_() & F_()/gg_()<=h_() & F_()/G_()<=h_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (x/y<=z <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(xx/yy<=z & xx/Y<=z & X/yy<=z & X/Y<=z))))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "pow<= up".
    *    f()^2<=h() <- ((ff()<=f() & f()<=F()) & (ff()^2<=h() & F()^2<=h()))
    * End.
    * }}}
    */

  lazy val intervalUpPower = derivedAxiom("pow<= up", Sequent(IndexedSeq(), IndexedSeq("f_()^2 <=h_() <- ((ff_()<=f_() & f_()<=F_()) & (ff_()^2 <= h_() & F_()^2 <=h_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall X \\forall z \\forall x (x^2<=z <- ((xx<=x & x<=X) & (xx^2<=z & X^2<=z)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=neg down".
    *    h<=-f() <- (f()<=F() & h() <= -F())
    * End.
    * }}}
    */

  lazy val intervalDownNeg = derivedAxiom("<=neg down", Sequent(IndexedSeq(), IndexedSeq("h_()<=-f_() <- (f_() <= F_() & h_() <= -F_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall z \\forall x (z<=-x <- (x<=X & z<=-X))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=abs down".
    *    h()<=abs(f()) <- ((ff()<=f() & f() <= F()) & (h()<=ff() | h()<=-F()))
    * End.
    * }}}
    */

  lazy val intervalDownAbs = derivedAxiom("<=abs down", Sequent(IndexedSeq(), IndexedSeq("h_()<=abs(f_()) <- ((ff_() <= f_() & f_() <= F_()) & (h_() <= ff_() | h_() <= -F_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable),("F_()".asTerm,"X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall xx \\forall z \\forall x (z<=abs(x) <- ((xx<=x & x <=X) & (z <= xx | z <= -X)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=max down".
    *    h()<=max(f(),g()) <- ((ff()<=f() & gg()<=g()) & (ff()<=h() | gg()<=h()))
    * End.
    * }}}
    */
  lazy val intervalDownMax = derivedAxiom("<=max down", Sequent(IndexedSeq(), IndexedSeq("h_() <= max(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() | h_() <= gg_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z <= max(x,y) <- ((xx<=x & yy<=y) & (z<=xx | z<=yy)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=min down".
    *    h()<=min(f(),g()) <- ((ff()<=f() & gg()<=g()) & (h()<=ff() & h()<=gg()))
    * End.
    * }}}
    */
  lazy val intervalDownMin = derivedAxiom("<=min down", Sequent(IndexedSeq(), IndexedSeq("h_()<=min(f_(),g_()) <- ((ff_()<=f_() & gg_()<=g_()) & (h_() <= ff_() & h_()<=gg_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=min(x,y) <- ((xx<=x & yy<=y) & (z<=xx & z<=yy)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=+ down".
    *    h()<=f()+g() <- ((ff()<=f() & gg()<=g()) & h()<=ff()+gg())
    * End.
    * }}}
    */
  lazy val intervalDownPlus = derivedAxiom("<=+ down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()+g_() <- ((ff_()<=f_() & gg_()<=g_()) & h_()<=ff_()+gg_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall z \\forall y \\forall x (z<=x+y <- ((xx<=x & yy<=y) & z<=xx+yy))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=- down".
    *    h()<=f()-g() <- ((ff()<=f() & g()<=G()) & h()<=ff()-G())
    * End.
    * }}}
    */
  lazy val intervalDownMinus = derivedAxiom("<=- down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()-g_() <- ((ff_()<=f_() & g_()<=G_()) & h_()<=ff_()-G_())".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("ff_()".asTerm, "xx".asVariable), ("G_()".asTerm, "Y".asVariable))(1) &
      byUS(proveBy("\\forall Y \\forall xx \\forall z \\forall y \\forall x (z<=x-y <- ((xx<=x & y<=Y) & z<=xx-Y))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=* down".
    *    h()<=f()*g()<- (((ff()<=f() & f()<=F()) & (gg()<=g() & g()<=G())) & (h()<=ff()*gg() & h()<=ff()*G() & h()<=F()*gg() & h()<=F()*G()))
    * End.
    * }}}
    */
  lazy val intervalDownTimes = derivedAxiom("<=* down", Sequent(IndexedSeq(), IndexedSeq("h_()<=f_()*g_()<- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & (h_()<=ff_()*gg_() & h_()<=ff_()*G_() & h_()<=F_()*gg_() & h_()<=F_()*G_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x*y<- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & (z<=xx*yy & z<=xx*Y & z<=X*yy & z<=X*Y)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=1Div down".
    *    h()<=1/f() <- ((f()<=F() & F()*f()>0) & (h()<=1/F()))
    * End.
    * }}}
    */
  lazy val intervalDown1Divide = derivedAxiom("<=1Div down", Sequent(IndexedSeq(), IndexedSeq("h_()<=1/f_() <- ((f_()<=F_() & F_()*f_()>0) & (h_()<=1/F_()))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "y".asVariable), ("F_()".asTerm, "X".asVariable))(1) &
      byUS(proveBy("\\forall X \\forall y \\forall x (y<=1/x <- ((x<=X & X*x>0) & (y<=1/X)))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "<=Div down".
    *    h() <= f()/g() <- ((ff()<=f() & f()<=F() & gg()<=g() & g()<=G()) & ((G()<0 | 0 < gg()) & (ff()/gg()<=h() & ff()/G()<=h() & F()/gg()<=h() & F()/G()<=h())))
    * End.
    * }}}
    */

//  lazy val intervalDownDivide = derivedAxiom("<=Div down", Sequent(IndexedSeq(), IndexedSeq(("h_() <= f_()/g_() <- (((ff_()<=f_() & f_()<=F_()) & (gg_()<=g_() & g_()<=G_())) & ((G_()<0 | 0 < gg_()) & (h_()<=ff_()/gg_() & h_()<=ff_()/G_() & h_()<=F_()/gg_() & h_()<=F_()/G_())))").asFormula)),
//    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("g_()".asTerm, "y".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("G_()".asTerm, "Y".asVariable), ("ff_()".asTerm, "xx".asVariable), ("gg_()".asTerm, "yy".asVariable))(1) &
//      byUS(proveBy("\\forall yy \\forall xx \\forall Y \\forall X \\forall z \\forall y \\forall x (z<=x/y <- (((xx<=x & x<=X) & (yy<=y & y<=Y)) & ((Y<0|0<yy) &(z<=xx/yy & z<=xx/Y & z<=X/yy & z<=X/Y))))".asFormula, TactixLibrary.RCF))
//  )

  /**
    * {{{Axiom "<=pow down".
    *    h()<=f()^2 <- ((ff()<=f() & f()<=F()) & ((0<= ff_() & h()<=ff()^2) | (F_() <0 & h()<=F()^2)))
    * End.
    * }}}
    */

  lazy val intervalDownPower = derivedAxiom("<=pow down", Sequent(IndexedSeq(), IndexedSeq("h_() <= f_()^2 <- ((ff_()<=f_() & f_()<=F_()) & ((0<= ff_() & h_() <= ff_()^2) | (F_()<=0 & h_() <= F_()^2)))".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable), ("h_()".asTerm, "z".asVariable), ("F_()".asTerm, "X".asVariable), ("ff_()".asTerm, "xx".asVariable))(1) &
      byUS(proveBy("\\forall xx \\forall X \\forall z \\forall x (z<=x^2 <- ((xx<=x & x<=X) & ((0 <= xx & z<=xx^2) | (X<= 0 & z<=X^2))))".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "dgZeroEquilibrium".
    *   x=0 & n>0 -> [{x'=c*x^n}]x=0
    * End.
    * }}}
    */
  //@note not derivable with Z3; added to AxiomBase and tested to be derivable in DerivedAxiomsTests.
//  lazy val dgZeroEquilibrium = derivedAxiom("dgZeroEquilibrium", Sequent(IndexedSeq(), IndexedSeq("x=0 & n>0 -> [{x'=c*x^n}]x=0".asFormula)),
//    implyR(1) & DA("y' = ( (-c*x^(n-1)) / 2)*y".asDifferentialProgram, "x*y^2=0&y>0".asFormula)(1) <(
//      TactixLibrary.QE,
//      implyR(1) & TactixLibrary.boxAnd(1) & andR(1) <(
//        DifferentialTactics.diffInd()(1) & QE,
//        DA("z' = (c*x^(n-1)/4) * z".asDifferentialProgram, "y*z^2 = 1".asFormula)(1) <(
//          QE,
//          implyR(1) & diffInd()(1) & QE
//        )
//      )
//    )
//  )

  // Metric Normal Form

  /**
    * {{{Axiom "= expand".
    *   f_()=g_() <-> f_()<=g_()&g_()<=f_()
    * End.
    * }}}
    */
  lazy val equalExpand: Lemma = derivedAxiom("= expand", Sequent(IndexedSeq(), IndexedSeq("f_()=g_() <-> f_()<=g_()&g_()<=f_()".asFormula)), QE & done)

  /**
    * {{{Axiom "!= expand".
    *   f_()!=g_() <-> f_()<g_()|g_()<f_()
    * End.
    * }}}
    */
  lazy val notEqualExpand: Lemma = derivedAxiom("!= expand", Sequent(IndexedSeq(), IndexedSeq("f_()!=g_() <-> f_()<g_()|g_()<f_()".asFormula)), QE & done)


  /**
    * {{{Axiom "<= to <".
    *   f_()<=0 <- f_()<0
    * End.
    * }}}
    */
  lazy val le2l: Lemma = derivedAxiom("<= to <", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 <- f_()<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <".
    *   f_()<g_() <-> f_()-g_()<0
    * End.
    * }}}
    */
  lazy val metricLess: Lemma = derivedAxiom("metric <", Sequent(IndexedSeq(), IndexedSeq("f_()<g_() <-> f_()-g_()<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <=".
    *   f_()<=g_() <-> f_()-g_()<=0
    * End.
    * }}}
    */
  lazy val metricLessEqual: Lemma = derivedAxiom("metric <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=g_() <-> f_()-g_()<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <= & <=".
    *   f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0
    * End.
    * }}}
    */
  lazy val metricAndLe: Lemma = derivedAxiom("metric <= & <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 & g_()<=0 <-> max(f_(), g_())<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric < & <".
    *   f_()<0 & g_()<0 <-> max(f_(), g_())<0
    * End.
    * }}}
    */
  lazy val metricAndLt: Lemma = derivedAxiom("metric < & <", Sequent(IndexedSeq(), IndexedSeq("f_()<0 & g_()<0 <-> max(f_(), g_())<0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric <= | <=".
    *   f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0
    * End.
    * }}}
    */
  lazy val metricOrLe: Lemma = derivedAxiom("metric <= | <=", Sequent(IndexedSeq(), IndexedSeq("f_()<=0 | g_()<=0 <-> min(f_(), g_())<=0".asFormula)), QE & done)

  /**
    * {{{Axiom "metric < | <".
    *   f_()<0 | g_()<0 <-> min(f_(), g_())<0
    * End.
    * }}}
    */
  lazy val metricOrLt: Lemma = derivedAxiom("metric < | <", Sequent(IndexedSeq(), IndexedSeq("f_()<0 | g_()<0 <-> min(f_(), g_())<0".asFormula)), QE & done)

  //Extra arithmetic axioms for SimplifierV3 not already included above

  /**
    * {{{Axiom "* identity neg".
    *    f()*-1 = -f()
    * End.
    * }}}
    */
  lazy val timesIdentityNeg = derivedAxiom("* identity neg", Sequent(IndexedSeq(), IndexedSeq("f_()*-1 = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) &
      byUS(proveBy("\\forall x (x*-1 = -x)".asFormula, TactixLibrary.RCF))
  )

  /**
    * {{{Axiom "-0".
    *    (f()-0) = f()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val minusZero = derivedAxiom("-0", Sequent(IndexedSeq(), IndexedSeq("(f_()-0) = f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (x-0 = x)".asFormula, TactixLibrary.RCF)))

  /**
    * {{{Axiom "0-".
    *    (0-f()) = -f()
    * End.
    * }}}
    *
    * @Derived
    */
  lazy val zeroMinus = derivedAxiom("0-", Sequent(IndexedSeq(), IndexedSeq("(0-f_()) = -f_()".asFormula)),
    allInstantiateInverse(("f_()".asTerm, "x".asVariable))(1) & byUS(proveBy("\\forall x (0-x = -x)".asFormula, TactixLibrary.RCF)))

  //TODO: add more text to the following
  lazy val gtzImpNez = derivedAxiom(">0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() > 0 -> f_()!=0".asFormula)), QE)
  lazy val ltzImpNez = derivedAxiom("<0 -> !=0", Sequent(IndexedSeq(), IndexedSeq("f_() < 0 -> f_()!=0".asFormula)), QE)

  lazy val zeroDivNez = derivedAxiom("!=0 -> 0/F", Sequent(IndexedSeq(), IndexedSeq("f_() != 0 -> 0/f_() = 0".asFormula)), QE)
  lazy val powZero = derivedAxiom("F^0", Sequent(IndexedSeq(), IndexedSeq("f_()^0 = 1".asFormula)), QE)
  lazy val powOne = derivedAxiom("F^1", Sequent(IndexedSeq(), IndexedSeq("f_()^1 = f_()".asFormula)), QE)

  // The following may already appear above
  // They are stated here in a shape suitable for the simplifier
  private def mkDerivedAxiom(name:String,f:Option[String],t:String,tt:String):Lemma =
  {
    val tfml = t.asFormula
    val ttfml  = tt.asFormula
    f match{
      case None => derivedAxiom(name,Sequent(IndexedSeq(),IndexedSeq(Equiv(tfml,ttfml))),prop & QE & done)
      case Some(f) => derivedAxiom(name,Sequent(IndexedSeq(),IndexedSeq(Imply(f.asFormula,Equiv(tfml,ttfml)))),prop & QE & done)
    }
  }

  //(Ir)reflexivity axioms for comparison operators
  lazy val lessNotRefl      = mkDerivedAxiom("< irrefl",  None,"F_()<F_()","false")
  lazy val greaterNotRefl   = mkDerivedAxiom("> irrefl", None,"F_()>F_()","false")
  lazy val notEqualNotRefl  = mkDerivedAxiom("!= irrefl",None,"F_()!=F_()","false")
  lazy val equalRefl        = mkDerivedAxiom("= refl",   None,"F_() = F_()","true")
  lazy val lessEqualRefl    = mkDerivedAxiom("<= refl",  None,"F_() <= F_()","true")
  lazy val greaterEqualRefl = mkDerivedAxiom(">= refl",  None,"F_() >= F_()","true")

  //(anti) symmetry axioms
  lazy val equalSym = mkDerivedAxiom("= sym",Some("F_() = G_()"),"G_() = F_()","true")
  lazy val notEqualSym = mkDerivedAxiom("!= sym",Some("F_() != G_()"),"G_() != F_()","true")
  lazy val greaterNotSym = mkDerivedAxiom("> antisym",Some("F_() > G_()"),"G_() > F_()","false")
  lazy val lessNotSym = mkDerivedAxiom("< antisym",Some("F_() < G_()"),"G_() < F_()","false")


  /**
    * {{{Axiom "all stutter".
    *    \forall x p <-> \forall x p
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  lazy val forallStutter: Lemma = derivedAxiom("all stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\forall x_ p_(x_) <-> \\forall x_ p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )

  /**
    * {{{Axiom "exists stutter".
    *    \exists x p <-> \exists x p
    * End.
    * }}}
    *
    * @Derived
    * @note Trivial reflexive stutter axiom, only used with a different recursor pattern in AxiomIndex.
    */
  lazy val existsStutter: Lemma = derivedAxiom("exists stutter",
    Sequent(IndexedSeq(), IndexedSeq("\\exists x_ p_(x_) <-> \\exists x_ p_(x_)".asFormula)),
    byUS(equivReflexiveAxiom)
  )
}
