<!-- Provenance: copied from the design workspace CambridgePQ/recursion.fast, `recursion-fast-idea-prompt.md`, on 2026-10-19. Read-only copy; the source is authoritative. -->
Context: I am planning on working on an autoresearch competition called recursion.fast, whose main objective is to produce a SNARK verifier specification which is as efficient as possible for proving arbitrary R1CS arithmetisation relations. This work will allow agents to submit verifier specification implementations and then produce Lean 4 proofs that this implementation is knowledge sound above a certain threshold and satisfies perfect (or imperfect) completeness. Many such similiar autoresearch challenges have been deployed for different ideas such as signature design exploration, improving quantum circuits for Shor's algorihtm and so on. An important property of the autoresearch competition is that the security definitions will be very readable and auditable to prevent agents from cheating, but will allow for a large design space exploration. The competition will have a submission repository which will allow people to open PRs for submissions (untrusted and possibly adversarial) and a verification repository which defines the rules and can be assumed to be trusted. We want to generate interesting verifier architecture designs.
 
Objective: Your job is to ome up with a comprehensive in-depth competition blueprint which explores and defines the following sections:
- High-level objective and design of the autoresearch competition. What is our aim, how do we plan on achieving it
- Competition rules, what needs to be verified by the CI, what can we trust, what do the autoresearch agents control, where the gaps are
- Submission format, how is the verifier submitted (RISCV, R1CS) so on, how do we assign a "cost" function to the performance of the verifier/honest prover. Can this cost function be gamed, what is an easy to implement cost function (it doesn't need to be perfect) that will accurately create incentives for autoresearch to produce interesting verifier specifications (rather than trivial/cheating ones)
- Security definitions, how do we ensure that the verifier specification is correct? What properties do we care about? Round-by-round knowledge soundness, perfect (or maybe imperfect completeness)
- What will our baseline be, this should a feasible MVP which can be checked on this machine within a feasible amount of time (< 1 hour)

Things to consider:
- You should assume that this will be an MVP, we don't necessarily need super accurate cost function/performance metric, the more accurate the better. But an MVP is suitable
- This should enable easy design space exploration, agents should be free to explore and come up with as many optimisation as possible
- With recursion in SNARKs, the verifier specification may change compared to the final layer verfieir and inner SNARK verifiers (in order to produce optimisations). We would ideally like a way to model such differences, an initial idea is to add a "Batcher" program which takes two proofs pi_1, pi_2 and generates a new proof pi' with the property that if a base verifier accepts pi_1 and pi_2, then it will accept pi' with overwhelmingly high probability (or something akin to this definition). (#1)
- Do we have a interactive or non-interactive protocol? Interactive protocols are easier to model, and are suitable for our current purposes.
- How do you prevent overfitting? We want a general verifier specification which can be used for generally arbitrary computation, a verifier which is super overfitted on the domain task is not an interesting output for the autoresearch competition. 


Current Idea:
The verifier will be generated in the form of a RISCV program which takes in a serialized proof, reads it and generates a true/false. Using Lean 4 and RISCV semantics, we will prove that this verifier reduces an arbitrary R1CS relation into Unit (true/false) and that comes with a honest prover (also in RISCV bytecode) which we use to prove completeness. This also includes a batcher (in RISCV) which we prove the definition as descriebd in (#1). The cost function is the following: we arithmetize hash chain computations (Blake or Sha) and the prover proves that they know the pre-images to the hash-chains, we will run the verifier/prover on thousands/millions of hash chain proofs and measure the median performance (or some type of average). We then divide this performance by the size of the RISCV verifier (+ batcher) programs to incentivise as an efficient and small of a verifier/batcher.

We can also take this one step further which you can consider is that we arithmetize the verifier, and direclty measure the wall-time of 2->1 recursion on its self. However, this may be much more ambitious because we will need to compile the RISCV into an R1CS circuit which may not be straightforward with the current model we have.

Resources:
- THe security definitions will be written in Lean 4 to ensure that the verifier/honest prover are correct. You should use the following repositories for ideas and motivation:
 (a) LeanerVM, this is an inprogress end-to-end formalisation of which uses upstream libraries ArkLib/VCV-io/CompPoly to define a SNARK relation and a verifier/prover specification with two master theorems
 (b) ots-golf, this is an autoresearch competition which attempts to design a one-time signature scheme, this will have a very similiar structure to what I have in mind, signature algorithms are submitted in RISCV and then proven secure/correct/faithful in Lean 4. Submission rules and definitons can be found at https://github.com/leanEthereum/ots.golf-dev/. I recommend for you to use the RISCV specification from this repository as a handy tool. You should also include additional ideas
(c) ArkLib, this is a library for writing SNARK PIOPs, and we should use to rigorously define the security definitions and properties of the verifier/prover specifications. It can be found both in the .lake/ build of the leanerVM repository and online at https://github.com/Verified-zkEVM/ArkLib.
 (d) sig.golf, this is very similiar to ots.golf but is more expansive and so has to deal with much larger proofs (which I recommend for you to look at to prevent huge build times/verification times). This autoresearch competition focuses on statless signatures, which is closer to complexity to a verifier SNAR. The repository can be fuond here: https://github.com/Layr-Labs/sig.golf-dev
 (e) better.codes, this uses ArkLib to define a toy IOP which is used for the proximity gap conjecture, this is very relevant as it defines an autoresearch compeititon using ArkLib, in a way that I recommend you use. https://github.com/proximity-prize/proximity-prize

Methodology: You are welcome to use Lean 4 probes and to clone the mentioned repositories (and the VerifiedzkEVM/riscv-zkvm repository). I recommend that you use subagents such as Opus 5.5 for probes/writing code and Fable 5.1 xhigh thinking for deep ideation. I highly recommend that you use adversarial reviews (Opus agents) to check the incetnvies/definitions of the competition/build times of proofs and whether we a. design an autoresearch competition which allows us to achieve optimised/interesting verifier architectures and b. small security definition auditability base, which can be read and understood by humans (use ots.golf, sig.golf as very strong inspiration) and c. reduces build/proof checking times as much as possible.

Work guidelines, best practices and priorities

This session is, for now, an exploratory and documentation session first. We want to make sure that we carefully compile, in a legible, maintainable, editable format all of the knowledge we can to then be in the best possible position to execute.
We must of course ensure to validate our work continuously as it progresses to catch any errors or drift early before it propagates. Thus execution is also part of the work and can be done once the underlying grounding and knowledge is in place.

Format of the final output

The output of this work should be a in .tex file for the sake of having an easily editable document to iterate on as required, and also to make full use of LaTeX's capabilities in representing all aspects of the work that will be analysed in this report.
There is no length limit for the report.
It must be thorough: details and precision are required to clearly communicate the work and its nuances without any gaps.
The writing must be clear, points must be both validated and illustrated, and conclusions must be reproducible.
Issues must be documented clearly in an information and actionable manner; this docuemnt also serves a pedagogical role.
References must be carefully cited.
Ensure that technical terms are clearly defined where appropriate to avoid confusion for any reader.
Think of this report as the kind that would be produced by an expert academic or consultant for a top tier publication or client report to a technical team.
Recall that the audience are world class cryptographers and zkVM engineers (two distinct groups) but may have limited familiarity with Lean and formal verification. Other readers may have significant formal verification expertise but may less familiar with the cryptography and implementation details of zkVMs. Make sure the report is useful to this variety of highly technical audience without dumbing it down or adding superfluous details and explanation.
Despite the lack of length limit, clarity and conciseness are paramount.
Orchestration and evaluation

This session's main agent is the orchestrator and final evaluator that will produce the final document.
Given the large scope of the task and numerous references, managing context is key.
The orchestrator will carefully coordinate independent sub-agents that will execute self-contained tasks: research and exploration, design and prototyping, validation and implementation, adversarial review, resolving issues and polishing work that passes cleanly through independent adversarial reviews. As the final evaluator, this session will be responsible to validate and produce the final technical document, so it mustg also have enough detailed context about every single item discussed in it, obtained via clean, polished, validated documentation that sub-agents with their won context will have been able to help produce without sacrificing the main agent's context window.
At all times, the quality of the work must be considered the highest priority rather than aiming to be faster or more efficient in resource/token usage. Web search is also available of course, as are any other useful tools available.
Execution

(1) Start by reviewing this prompt critically: is there anything that can be clarified, scope that is missing, or anything else to improve this prompt? Web search and a deep research may also help provide some grounding fort he work, but it must be ensured that is it a useful deep research ad old references may no longer be relevant and may distract from present realities.
(2) Plan the work in a detailed manner. Scaffold the report document (sections and outlines), determine a complete set of sub-tasks, assess any repository that must be built before starting.
(3) Execute the plan, invoking sub-agents as required for independent tasks. Make sure to consistently evaluate and validate your work and that of other agents adversarially; review continuously via adversarial review agents rather than waiting for the end to review.
This is a large task! There is both a significant scope to this task and with resect to the references available (see repositories, references in the state of zk tooling paper, ...) which could also be supplemented by a deep research. But this task is nonetheless crucial to get right, issues in the work or our understanding of it could lead to critical incidents in deployments of recursion.fast.do not worry about resource efficiency, only about the task and hand and producing the highest possible quality output that will help have the highest possible level of assurance in a future deployment of recursion.fast.
