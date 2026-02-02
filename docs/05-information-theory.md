# Information Theory and Channels

This document covers the information-theoretic machinery in Gibbs. Shannon entropy, KL divergence, and channel capacity provide the language for reasoning about communication under noise. These concepts connect to convex duality through the entropy-Bregman correspondence, and to consensus through the coding-theoretic bridge. See [Convex Duality and Bregman Divergence](03-convex-duality.md) for the duality perspective and [Consensus as Statistical Mechanics](06-consensus-statistical-mechanics.md) for the application to agreement protocols.

## Entropy and KL Divergence

Shannon entropy measures uncertainty in a discrete distribution $p$ over a finite set:

$$H(p) = -\sum_i p_i \log p_i$$

Entropy is nonneg (`shannonEntropy_nonneg`) and zero for deterministic distributions (`shannonEntropy_deterministic`). It is maximized by the uniform distribution.

The KL divergence measures how one distribution $p$ differs from another $q$:

$$D_{\mathrm{KL}}(p \| q) = \sum_i p_i \log \frac{p_i}{q_i}$$

The Gibbs inequality states $D_{\mathrm{KL}}(p \| q) \geq 0$, proved in `klDivergence_nonneg` using the bound $\log x \leq x - 1$. KL divergence equals zero if and only if $p = q$.

Mutual information $I(X; Y)$ quantifies shared information between two random variables. It decomposes as $I(X; Y) = H(X) - H(X|Y)$, where $H(X|Y)$ is conditional entropy. The theorem `condEntropy_le_entropy` shows conditioning cannot increase entropy. Mutual information is symmetric: `mutualInfo_symm`.

## Discrete Memoryless Channels

A discrete memoryless channel (DMC) is a stochastic matrix $W(y|x)$ mapping input symbols to output symbols. The `DMC` structure stores this matrix with the constraint that each row sums to one.

Given an input distribution $p$ and channel $W$, the induced output distribution is $q(y) = \sum_x p(x) W(y|x)$. The joint distribution factorizes as $p(x) W(y|x)$. The theorems `jointDist_marginalFst` and `jointDist_marginalSnd` recover the input and output marginals.

Channel capacity is the maximum mutual information over all input distributions:

$$C = \sup_p I(p; W)$$

Capacity is nonneg (`channelCapacity_nonneg`). It is bounded above by $\log |\mathcal{X}|$ and $\log |\mathcal{Y}|$. The data processing inequality states that post-processing cannot increase mutual information. These bounds are stated as axioms in `Entropy.lean`.

## The Binary Symmetric Channel

The BSC with crossover probability $\varepsilon$ flips each bit independently with probability $\varepsilon$. Its capacity is:

$$C_{\mathrm{BSC}} = 1 - H_2(\varepsilon)$$

where $H_2$ is binary entropy. At $\varepsilon = 0$, capacity is 1 (perfect channel). At $\varepsilon = 1/2$, capacity is 0 (the channel destroys all information). The axioms `bsc_capacity` and `bsc_capacity_half` formalize these.

The BSC is the channel-theoretic model for random bit corruption. In the consensus context, $\varepsilon$ plays the role of the corruption fraction. The zero-capacity point $\varepsilon = 1/2$ corresponds to the impossibility threshold.

## The Coding Bridge

Error-correcting codes are the static (non-interactive) case of the consensus framework. A code of length $N$ encodes messages into codewords. The minimum Hamming distance $d_{\min}$ between distinct codewords determines correction capability.

Unique decoding succeeds when the number of errors $t$ satisfies $2t < d_{\min}$. The theorem `unique_decoding_of_minDistance` in `CodingDistance.lean` formalizes this. Hamming distance instantiates the `EnergyDistance` class, and `energyGap_singleton_eq_dist` shows the energy gap between singleton codeword sets equals their distance.

The repetition code encodes one bit as $N$ identical copies. Majority vote decodes. The theorem `repetition_corrects_up_to` proves correction of up to $\lfloor(N-1)/2\rfloor$ errors. This is the simplest gapped phase: the distance between the two codewords is $N$, creating a macroscopic energy barrier.

## Gaussian Channels and Spatial Capacity

The Gaussian channel adds noise with variance $\sigma^2$. Its capacity under power constraint $P$ is:

$$C = \frac{1}{2} \log\left(1 + \frac{P}{\sigma^2}\right)$$

Capacity is nonneg for nonneg power (`gaussianCapacity_nonneg`), monotone decreasing in noise variance (`gaussianCapacity_antitone_variance`), and monotone increasing in power (`gaussianCapacity_monotone_power`).

Noise variance and inverse temperature are interchangeable through the mapping $\beta = 1/(2\sigma^2)$. The round-trip identity `noiseToInvTemp_invTempToNoise` confirms this bijection. Higher inverse temperature (lower noise) means higher capacity (`capacity_monotone_invTemp`).

For spatially embedded systems, channel capacity depends on the distance between communicating roles. The `SpatialChannelModel` structure specifies signal power and a distance-dependent noise function. The theorem `spatialCapacity_antitone` shows capacity decreases with distance. Colocated roles achieve maximum capacity (`colocated_max_capacity`).
