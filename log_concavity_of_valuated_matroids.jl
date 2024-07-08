################# Logarithmic concavity of valuated matroids ############################
#                                                                                       #
#       Jeffrey Giansiracusa, Felipe Rincon, Victoria Schleis, and Martin Ulirsch       #
#       Accompanying code to the paper "Logarithmic concavity of valuated matroids"     #
#                                   arxiv::                                             #
#                                                                                       #
#########################################################################################

##################### General setup #####################################################

# Set up the Puiseux series and their valuation in the standard way, and set up infinity
# Create a list of nonrealizable matroids

Kt,t = rational_function_field(QQ,"t");
nu_t = tropical_semiring_map(Kt,t)
infty = nu_t(0)

fano  = [nu_t.(Kt.(Int.([in(i,bases(fano_matroid())) for i in AbstractAlgebra.combinations(7,3)]))),3,7]
vamos = [nu_t.(Kt.(Int.([in(i,bases(vamos_matroid())) for i in AbstractAlgebra.combinations(8,4)]))),4,8]
nonpappus = [nu_t.(Kt.(Int.([in(i,bases(non_pappus_matroid())) for i in AbstractAlgebra.combinations(9,3)]))),3,9]

nonrealiz = [fano, vamos,nonpappus]

#########################################################################################
#                                Main functions                                         #
#########################################################################################

# The following two functions are the main functions used for the paper. 

# random_check_concavity checks ultra log concavity for randomly generated realizable 
# matroids of rank at least 4 over ground sets of size at least 4, successively increasing
# the rank and the ground set size. 

# Input: i is the maximal rank of the realizable matroids you want to check
#        j is the maximal ground set size of the realizable matroids you want to check
#        step is the number of samples one wants to take for a pair (i,j).
#        a is the numerical accuracy you want the violated inequality to have.

# Returns:  a pluecker vector and a float 0 < q < 1 for which ultra log concavity on the 
#           independent sets is violated, and the entry in the sequence for which it is.    

# Runtime suggestions:  Code runs quickly until about ground set size 13, whereas 14 and
#                       15 are noticeably more computationally intensive. we suggest 
#                       i = 10 and j = 15. We suggest a to be chosen around 0.0005.
#                       We usually choose step to be 10000.


function random_check_concavity(i::Int64,j::Int64, step::Int64, a::Float64)
    for n in 4:i
        for m in n+1:j
            println(m,n) 
            for i in 1:step
                f = random_pluecker_vector(n,m)
                v = is_ultra_log_concave_pl(f,n,m,a)
                if !(v[1][1])
                    return (f,v[2],v[1][2])
                end
            end
        end
    end
end



# random_check_concavity checks ultra log concavity for the direct sum of a nonrealizable
# matroid, taken from the input list nonrealiz, with a randomly
# generated realizable matroid. Randomly generated realizable matroids are of rank at 
# least 1 over ground sets of size at least 2, again successively increasing the rank and 
# the ground set size. 

# Input:    i is the maximal rank of the realizable matroids you want to add
#           j is the maximal ground set size of the realizable matroids you want to add
#           step is the number of samples one wants to take for a pair (i,j).
#           a is the numerical accuracy you want the violated inequality to have.
#           nonrealiz is a vector of nonrealizable matroids, with their rank and ground
#               set size.

# Returns:  a pluecker vector and a float 0 < q < 1 for which ultra log concavity on the 
#           independent sets is violated, and the entry in the sequence for which it is.            


# Runtime suggestions:  Code runs quickly until about direct sum ground set size 13, whereas 14 and
#                       15 are noticeably more computationally intensive. we suggest 
#                       i = 5 and j = 5. We suggest a to be chosen around 0.0005.
#                       We usually choose step to be 10000.


function random_check_concavity_nr(i::Int64,j::Int64, step::Int64, a::Float64,nonrealiz)
    for nonr in nonrealiz
        for n in 1:i
            for m in n+1:j
                println(m,n) # prints which rank and ground set size we're currently at
                for i in 1:step
                    f,r,gs = random_pluecker_vector_nr(nonr,n,m)
                    v = is_ultra_log_concave_pl(f,r,gs,a)
                    if !(v[1][1])
                        return (f,v[2],v[1][2])
                    end
                end
            end
        end
    end
end



##################### Checking log concavity ############################################


# Returns whether a (finite) sequence l is log concave within a numerical accuracy bound a

function is_log_concave(l::Vector{Float64},a::Float64)
    k = length(l)
    for i in 2:k-1
        if l[i]*l[i] < l[i-1] * l[i+1]
            if  l[i-1] * l[i+1] - l[i]*l[i] > a
                println(i)
                return (false, l[i]*l[i]- l[i-1] * l[i+1])
            end
        end
    end
    return true
end



# Returns whether a (finite) sequence l is ultra log concave for binomials over m, within
# a numerical accuracy bound a

function is_ultra_log_concave(l::Vector{Float64},m::Int64,a::Float64)
    return is_log_concave([l[i]/binomial(m,i) for i in 1:length(l)],a)
end



# Returns whether the independent set sequence (see Theorem A) associated to a valuated 
# matroid of rank r over [n], given as a pluecker vector pl is ultra log concave with 
# numerical accuracy a

function is_ultra_log_concave_pl(pl::Vector{TropicalSemiringElem{typeof(min)}},r::Int64,n::Int64,a::Float64)
    out = Vector{Float64}([])
    q = rand()
    for k in 1:r
        ind_s = indep_sets_pl(pl,k,r,n)
        if length(ind_s) == 0
            return true ## returns true if matroid does not have expected rank. This is to rule out false positives
        end
        ind_vec= [valuation_indep_set_pl(I,pl,r,n) for I in ind_s]
        push!(out, sum([q^i for i in (Float64.(QQ.(ind_vec)))]))
    end
    return (is_ultra_log_concave(out,n,a),q)
end


##################### Random generation of valuated matroids #############################


# Generates the pluecker vector of a random realizable matroid of rank n over [m] by 
# generating a random matrix over the Puiseux series and computing its minors.

function random_pluecker_vector(n::Int64,m::Int64)
    A = [rand(vcat(zeros(Int,9),collect(1:9)))*t^(rand(vcat(zeros(Int,9),collect(1:9))))+rand(vcat(zeros(Int,9),collect(1:9)))*t^(rand(vcat(zeros(Int,9),collect(1:9)))) for i in  1:n*m]
    A = reshape(A,n,m)
    return nu_t.(minors(matrix(Kt,A),n))
end

# Generates the pluecker vector of a nonrealizable matroid obtained as the direct sum of 
# a nonrealizable matroid saved in the vector nonrealiz and a random realizable 
# matroid of rank n over [m]

function random_pluecker_vector_nr(nonr_matr,n::Int64,m::Int64)
    return direct_sum_pl(nonr_matr[1], nonr_matr[2],nonr_matr[3], random_pluecker_vector(n,m),n,m)
end

##################### Double check ######################################################

# (Inefficient) methods that can be used to double check a suspected counter-example. Not 
# suitable for a massive search. Their purpose is ruling out "counter-examples" that are 
# due to numerical rounding errors



# Generates the independence sequence of a valuated matroid of rank n over [m] given as a
# pluecker vector pl as a univariate polynomial in q

function generate_indep_sequence_as_poly_in_q(pl::Vector{TropicalSemiringElem{typeof(min)}},n::Int,m::Int)
    Kq, q = polynomial_ring(QQ, :q)
    q_poly = Kq(0)
    for k in 1:n
        for i in indep_sets_pl(pl,k,n,m)
            expo = ZZ(valuation_indep_set_pl(i,pl,n,m))
            q_poly = q_poly + ((QQ(1)/QQ(binomial(m,k)))*q^expo)
        end
    end
    return q_poly
end


# Checks ultra log concavity at a sequence value k by computing roots of  I_k^2 - I_k-1 * I_k+1.
# If these are in (0,1], we have found a counterexample. We use this to rule out numerical error
# for very small values of q.

function ultra_log_concavity_double_check(k::Int,pl::Vector{TropicalSemiringElem{typeof(min)}},n::Int,m::Int)
    Kq, q = polynomial_ring(QQ, :q)
    q_poly_k = Kq(0)
    for i in indep_sets_pl(pl,k,n,m)
        expo = ZZ(valuation_indep_set_pl(i,pl,n,m))
        q_poly_k = q_poly_k + ((QQ(1)/QQ(binomial(m,k)))*q^expo)
    end

    q_poly_k_neg = Kq(0)
    for i in indep_sets_pl(pl,k-1,n,m)
        expo = ZZ(valuation_indep_set_pl(i,pl,n,m))
        q_poly_k_neg = q_poly_k_neg + ((QQ(1)/QQ(binomial(m,k-1)))*q^expo)
    end

    q_poly_k_pos = Kq(0)
    for i in indep_sets_pl(pl,k+1,n,m)
        expo = ZZ(valuation_indep_set_pl(i,pl,n,m))
        q_poly_k = q_poly_k + ((QQ(1)/QQ(binomial(m,k+1)))*q^expo)
    end
    return  roots((q_poly_k_neg*q_poly_k_pos) - (q_poly_k)^2)
end


#########################################################################################
#                            Auxiliary functions                                        #
#########################################################################################
# A collection of auxiliary functions, mainly utils to deal with valuated matroids saved #
# as pluecker vectors                                                                   #
#########################################################################################


# Determines the independent sets of size k of a matroid or rank r over the ground 
# set [n], given as a Pluecker vector pl    

function indep_sets_pl(pl::Vector{TropicalSemiringElem{typeof(min)}},k::Int64,r::Int64,n::Int64)
    coords = collect(AbstractAlgebra.combinations(n,r))
    nonzero = findall(i->i!=infty, pl)
    indep = Vector{Vector{Int64}}([])
    for j in nonzero
        append!(indep, collect(AbstractAlgebra.combinations(coords[j],k)))
    end
    return unique!(indep)
end



# Computes the (Murota) valuation of an independent set ind in the valuated matroid given by
# a pluecker vector pl of rank  r over [n]

function valuation_indep_set_pl(ind::Vector{Int64},pl::Vector{TropicalSemiringElem{typeof(min)}}, r::Int64,n::Int64)
    coords = collect(AbstractAlgebra.combinations(n,r))
    indices = findall(i -> is_subset(ind,i), coords)
    if length(indices)>0 
        return minimum(pl[indices])
    else   
        return infty
    end
end


# Determines the pluecker vector of the matroid arising as the direct sum of the matroids 
# corresponding to the pluecker vectors pl1 and pl2. r1 is the rank of the matroid associated
# to pl1, and [n1] is its ground set. Analogous for r2 and n2
function direct_sum_pl(pl1::Vector{TropicalSemiringElem{typeof(min)}},r1::Int64,n1::Int64,pl2::Vector{TropicalSemiringElem{typeof(min)}},r2::Int64,n2::Int64)
    r = r1+r2
    n = n1+n2
    res = Vector{TropicalSemiringElem{typeof(min)}}([])
    coords = collect(AbstractAlgebra.combinations(n,r))
    f = Dict(i => (i-n1) for i in (n1+1):n)
    for co in coords 
        base_m1 = filter(i -> i<n1+1, co)
        base_m2 = [get(f,i,n) for i in filter(i -> i>n1, co)]
        push!(res,valuation_indep_set_pl(base_m1,pl1,r1,n1)*valuation_indep_set_pl(base_m2,pl2,r2,n2))
    end
    return res,r,n
end




