---- MODULE PhoenixContract ----

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    INITIAL_TIER_ONE_KEY,
    INITIAL_TIER_TWO_KEY,
    BALANCE_LIMIT,
    OWNER_ADDRESS,
    ADVERSARY_ADDRESS,
    ADDRESSES,
    MONEY,
    MAX_BLOCK_NUMBER,
    REQUEST_IDS,
    DELAY_CONST,
    NETWORK_ADDRESSES,
    SIMULATE_EVENT

ASSUMPTION BALANCE_LIMIT \in Nat
ASSUMPTION ADDRESSES \subseteq Nat
ASSUMPTION MONEY \subseteq Nat
ASSUMPTION MAX_BLOCK_NUMBER \in Nat
ASSUMPTION REQUEST_IDS \subseteq Nat
ASSUMPTION DELAY_CONST \in Nat
ASSUMPTION INITIAL_TIER_ONE_KEY \in ADDRESSES
ASSUMPTION INITIAL_TIER_TWO_KEY \in ADDRESSES
ASSUMPTION OWNER_ADDRESS \in NETWORK_ADDRESSES
ASSUMPTION ADVERSARY_ADDRESS \in NETWORK_ADDRESSES

VARIABLES
    balance,                          \* F
    block_number,                     
    tier_one_addresses,               \* T1
    tier_two_addresses,               \* T2
    delay,                            \* D
    unlock_block,                     \* U
    requests,                         \* R
    owner_known_addresses,
    adversary_known_addresses

special_vars == <<owner_known_addresses, adversary_known_addresses>>

request_type == \* (id, amount, creation, initiator, recipient)
    REQUEST_IDS 
    \X MONEY 
    \X (0..MAX_BLOCK_NUMBER)
    \X ADDRESSES
    \X NETWORK_ADDRESSES

TypeOK ==
    /\ balance \in [NETWORK_ADDRESSES -> 0..BALANCE_LIMIT]
    /\ block_number \in 0..MAX_BLOCK_NUMBER
    /\ tier_one_addresses \in SUBSET ADDRESSES
    /\ tier_two_addresses \in SUBSET ADDRESSES
    /\ (tier_one_addresses \intersect tier_two_addresses) = {}
    /\ delay \in 0..MAX_BLOCK_NUMBER
    /\ unlock_block \in 0..MAX_BLOCK_NUMBER
    /\ requests \in SUBSET request_type
    /\ owner_known_addresses \in SUBSET ADDRESSES
    /\ adversary_known_addresses \in SUBSET ADDRESSES

vars == <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, special_vars>>

Init ==
    /\ balance = [addr \in NETWORK_ADDRESSES |-> 0]
    /\ block_number = 0
    /\ tier_one_addresses = {INITIAL_TIER_ONE_KEY}
    /\ tier_two_addresses = {INITIAL_TIER_TWO_KEY}
    /\ delay = DELAY_CONST
    /\ unlock_block = 0
    /\ requests = {}
    /\ owner_known_addresses = {INITIAL_TIER_ONE_KEY, INITIAL_TIER_TWO_KEY}
    /\ adversary_known_addresses = {}

--------------------------------------
\* Actions

Tick ==
    /\ block_number + 1 <= MAX_BLOCK_NUMBER
    /\ block_number' = block_number + 1

Sum ==
    LET red[rs \in SUBSET requests] == 
        IF rs = {} THEN 0
        ELSE 
            LET x == CHOOSE x \in rs: TRUE IN 
                x[2] + red[rs \ {x}]
    IN red[requests]

GetIds == 
    {req[1] : req \in requests}

GetRequestById(id) ==
    CHOOSE req \in {req \in requests: req[1] = id} : TRUE

GetCreationByID(id) ==
    GetRequestById(id)[3]

GetAmountByID(id) ==
    GetRequestById(id)[2]

GetAddressByID(id) ==
    GetRequestById(id)[5]

FilterNotByInitiator(initiator) ==
    {req \in requests: req[4] /= initiator}
                
Deposit(amount) ==
    /\ Tick
    /\ owner_known_addresses \intersect tier_one_addresses /= {}    /\ amount > 0
    /\ balance[OWNER_ADDRESS] + amount <= BALANCE_LIMIT
    /\ balance' = [balance EXCEPT ![OWNER_ADDRESS] = @ + amount]
    /\ UNCHANGED <<tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, special_vars>>

Request(address2, amount, recipient) ==
    /\ Tick
    /\ recipient /= OWNER_ADDRESS
    /\ recipient /= 0
    /\ amount > 0
    /\ Sum + amount <= balance[OWNER_ADDRESS]
    /\ balance[recipient] + amount <= BALANCE_LIMIT
    /\ address2 \in tier_two_addresses
    /\ requests' = requests \union {<<block_number, amount, block_number, address2, recipient>>}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

Withdraw(id) == 
    /\ unlock_block <= block_number
    /\ block_number < MAX_BLOCK_NUMBER
    /\ id \in GetIds
    /\ GetAddressByID(id) /= OWNER_ADDRESS
    /\ GetCreationByID(id) + delay <= block_number
    /\ LET balance1 == [balance EXCEPT ![OWNER_ADDRESS] = @ - GetAmountByID(id)]
       IN balance' = [balance1 EXCEPT ![GetAddressByID(id)] = @ + GetAmountByID(id)]
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<tier_one_addresses, block_number, tier_two_addresses, delay, unlock_block, special_vars>>
 
CancelRequest(address1, id) == 
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ id \in GetIds
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

CancelAllRequests(address1) ==
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ requests' = {}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

CancelSelfRequest(address2, id) ==
    /\ Tick
    /\ address2 \in tier_two_addresses
    /\ id \in GetIds
    /\ GetRequestById(id)[4] = address2
    /\ requests' = requests \ {GetRequestById(id)}
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, special_vars>>

Lock(address1, new_unlock_block) ==
    /\ Tick
    /\ SIMULATE_EVENT /= "tier_one_key_loss"
    /\ address1 \in tier_one_addresses
    /\ new_unlock_block <= MAX_BLOCK_NUMBER
    /\ new_unlock_block > unlock_block
    /\ new_unlock_block > block_number
    /\ unlock_block' = new_unlock_block
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, requests, special_vars>>
    
AddTierOneAddress(address1, new_address1) == 
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ new_address1 \notin tier_one_addresses
    /\ new_address1 \notin tier_two_addresses
    /\ tier_one_addresses' = tier_one_addresses \union {new_address1}
    /\ owner_known_addresses' = owner_known_addresses \union {new_address1}
    /\ UNCHANGED <<balance, tier_two_addresses, delay, unlock_block, requests, adversary_known_addresses>>

AddTierTwoAddress(address1, new_address2) == 
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ owner_known_addresses' = owner_known_addresses \union {new_address2}
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, requests, adversary_known_addresses>>

RemoveTierTwoAddress(address1, remove_address2) == 
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ remove_address2 \in tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \ {remove_address2}
    /\ owner_known_addresses' = owner_known_addresses \ {remove_address2}
    /\ requests' = FilterNotByInitiator(remove_address2)
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, adversary_known_addresses>>

OwnerAction ==
    \/ \E amount \in MONEY: 
        Deposit(amount)
    \/ \E <<address2, amount, recipient>> \in owner_known_addresses \X MONEY \X (NETWORK_ADDRESSES \ {ADVERSARY_ADDRESS}):
        Request(address2, amount, recipient)
    \/ \E id \in REQUEST_IDS: 
        Withdraw(id) 
    \/ \E <<address1, id>> \in owner_known_addresses \X REQUEST_IDS: 
        CancelRequest(address1, id)
    \/ \E address1 \in owner_known_addresses: 
        CancelAllRequests(address1) 
    \/ \E <<address2, id>> \in owner_known_addresses \X REQUEST_IDS: 
        CancelSelfRequest(address2, id) 
    \/ \E <<address1, new_unlock_block>> \in owner_known_addresses \X (0..MAX_BLOCK_NUMBER): 
        Lock(address1, new_unlock_block)
    \/ \E <<address1, new_address1>> \in owner_known_addresses \X ADDRESSES: 
        AddTierOneAddress(address1, new_address1)
    \/ \E <<address1, new_address2>> \in owner_known_addresses \X ADDRESSES: 
        AddTierTwoAddress(address1, new_address2)
    \/ \E <<address1, remove_address2>> \in owner_known_addresses \X ADDRESSES: 
        RemoveTierTwoAddress(address1, remove_address2) 

TierOneKeyLoss(address) ==
    /\ SIMULATE_EVENT = "tier_one_key_loss"
    /\ block_number < MAX_BLOCK_NUMBER - delay
    /\ Cardinality(owner_known_addresses) > 1
    /\ address \in owner_known_addresses
    /\ address \in tier_one_addresses
    /\ owner_known_addresses' = owner_known_addresses \ {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, adversary_known_addresses>>

TierTwoKeyLoss(address) ==
    /\ SIMULATE_EVENT = "tier_two_key_loss"
    /\ block_number < MAX_BLOCK_NUMBER
    /\ Cardinality(owner_known_addresses) > 1
    /\ address \in owner_known_addresses
    /\ address \in tier_two_addresses
    /\ owner_known_addresses' = owner_known_addresses \ {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, adversary_known_addresses>>

AddTierTwoAddressForAdversary(address1, new_address2) == 
    /\ Tick
    /\ address1 \in tier_one_addresses
    /\ new_address2 \notin tier_one_addresses
    /\ new_address2 \notin tier_two_addresses
    /\ tier_two_addresses' = tier_two_addresses \union {new_address2}
    /\ adversary_known_addresses' = adversary_known_addresses \union {new_address2}
    /\ UNCHANGED <<balance, tier_one_addresses, delay, unlock_block, requests, owner_known_addresses>>

TypeOneAttack(address) ==
    /\ SIMULATE_EVENT = "type_one_attack"
    /\ address \in tier_one_addresses
    /\ adversary_known_addresses' = adversary_known_addresses \union {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, owner_known_addresses>>

TypeTwoAttack(address) ==
    /\ SIMULATE_EVENT = "type_two_attack"
    /\ address \in tier_two_addresses
    /\ adversary_known_addresses' = adversary_known_addresses \union {address}
    /\ UNCHANGED <<balance, block_number, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, owner_known_addresses>>

AdversaryAction == 
    \/ \E <<address2, amount>> \in adversary_known_addresses \X MONEY:
        Request(address2, amount, ADVERSARY_ADDRESS)
    \/ \E id \in REQUEST_IDS: 
        Withdraw(id) 
    \/ \E <<address1, id>> \in adversary_known_addresses \X REQUEST_IDS: 
        CancelRequest(address1, id)
    \/ \E address1 \in adversary_known_addresses: 
        CancelAllRequests(address1) 
    \/ \E <<address2, id>> \in adversary_known_addresses \X REQUEST_IDS: 
        CancelSelfRequest(address2, id) 
    \/ \E <<address1, new_address2>> \in adversary_known_addresses \X ADDRESSES: 
        AddTierTwoAddressForAdversary(address1, new_address2)
    \/ \E <<address1, remove_address2>> \in adversary_known_addresses \X ADDRESSES: 
        RemoveTierTwoAddress(address1, remove_address2) 

EnvironmentAction ==
    \/ \E address \in ADDRESSES: 
        TierOneKeyLoss(address)
    \/ \E address \in ADDRESSES: 
        TierTwoKeyLoss(address)
    \/ \E address \in ADDRESSES: 
        TypeOneAttack(address)
    \/ \E address \in ADDRESSES: 
        TypeTwoAttack(address)

ActionTick ==
    /\ Tick
    /\ UNCHANGED <<balance, tier_one_addresses, tier_two_addresses, delay, unlock_block, requests, special_vars>>
Actions ==
    \/ OwnerAction 
    \/ AdversaryAction
    \/ EnvironmentAction
    \/ ActionTick

TierOneLossDefence1 ==
    /\ balance[OWNER_ADDRESS] > 0
    /\ \E <<address2, recipient>> \in owner_known_addresses \X (NETWORK_ADDRESSES \ {ADVERSARY_ADDRESS}):
        Request(address2, balance[OWNER_ADDRESS] - Sum, recipient) 

TierOneLossDefence2 ==
    /\ requests /= {}
    /\ \E req \in requests:
        Withdraw(req[1])

TierOneLossDefence ==
    /\ SIMULATE_EVENT = "tier_one_key_loss"
    /\ block_number <= MAX_BLOCK_NUMBER
    /\ balance[OWNER_ADDRESS] > 0
    /\ owner_known_addresses \intersect tier_one_addresses = {}
    /\ (
        \/ TierOneLossDefence1 
        \/ TierOneLossDefence2 
        \/ (~(ENABLED (TierOneLossDefence1 \/ TierOneLossDefence2)) /\ ActionTick))

TierTwoLossDefence == 
    /\ SIMULATE_EVENT = "tier_two_key_loss"
    /\ block_number < MAX_BLOCK_NUMBER
    /\ owner_known_addresses \intersect tier_two_addresses = {}
    /\ \E <<address1, new_address2>> \in owner_known_addresses \X ADDRESSES: 
        AddTierTwoAddress(address1, new_address2)

TypeOneAttackDefence ==
    /\ SIMULATE_EVENT = "type_one_attack"
    /\ \E <<address1, req>> \in owner_known_addresses \X requests: 
        /\ req[5] = ADVERSARY_ADDRESS
        /\ Lock(address1, MAX_BLOCK_NUMBER)

TypeTwoAttackDefence ==
    /\ SIMULATE_EVENT = "type_two_attack"
    /\ \E <<address1, req>> \in owner_known_addresses \X requests: 
        /\ req[5] = ADVERSARY_ADDRESS
        /\ RemoveTierTwoAddress(address1, req[4])

Defence ==
    \/ TierOneLossDefence
    \/ TierTwoLossDefence
    \/ TypeOneAttackDefence
    \/ TypeTwoAttackDefence

Next == 
    IF ENABLED Defence
    THEN Defence
    ELSE Actions \/ ActionTick

Spec == Init /\ [][Next]_vars

Fairness ==
    WF_vars(Actions)

FairSpec == Spec /\ Fairness

--------------------------------------
\* PROPERTIES

RecoversTierOneKeyLoss ==
    [](SIMULATE_EVENT = "tier_one_key_loss" /\ owner_known_addresses \intersect tier_one_addresses = {} 
        => <>[](balance[OWNER_ADDRESS] = 0))

RecoversTierTwoKeyLoss == 
    [](block_number < MAX_BLOCK_NUMBER /\ SIMULATE_EVENT = "tier_two_key_loss" /\ owner_known_addresses \intersect tier_two_addresses = {}
        => <>(owner_known_addresses \intersect tier_two_addresses /= {}))

AttacksFail ==
    [](balance[ADVERSARY_ADDRESS] = 0)

\* 1. Base layer
\* 1.1.
CannotWithdrawBeforeDelay ==
    [](\A r \in requests: (r[3] + delay > block_number => ~ENABLED Withdraw(r[1])))
\* 1.2.
TierOneCanCancelAnyRequestAnyTime ==
    [](block_number < MAX_BLOCK_NUMBER
        => \A <<address1, req>> \in tier_one_addresses \X requests: ENABLED CancelRequest(address1, req[1]))
\* 1.3.
CannotChangeDelay ==
    \E d \in 0..MAX_BLOCK_NUMBER: [](delay = d)
\* 1.4.
CannotRemoveTierOneAddress == 
    [][\A a \in ADDRESSES: a \in tier_one_addresses => a \in tier_one_addresses']_<<tier_one_addresses>>
\* 1.5.
CannotBeDestroyedUnlessEmpty ==
    <>[](balance[OWNER_ADDRESS] = 0)

\* 2. Key separation layer
\* 2.1.
TierOneAndTwoSeparated == 
    [](tier_one_addresses \intersect  tier_two_addresses = {})
\* 2.2.
OnlyTierOneCanAddTierOne ==
    [](\A address \in ADDRESSES: address \notin tier_one_addresses 
        => \A new_address1 \in ADDRESSES: ~ENABLED AddTierOneAddress(address, new_address1))
\* 2.3.
OnlyTierTwoCanRequest ==
    [](\A address \in ADDRESSES: address \notin tier_two_addresses 
        => \A <<amount, recipient>> \in MONEY \X NETWORK_ADDRESSES: ~ENABLED Request(address, amount, recipient))
\* 2.4.
TierTwoCanCancelOnlyItselfRequests ==
    [](\A address \in ADDRESSES: address \in tier_two_addresses 
        => \A req \in requests: req[4] /= address => ~ENABLED CancelSelfRequest(address, req[1]))
    
\* 3. Recovery layer
\* 3.1.
MoneyCannotLeaveLocked ==
    [](block_number < unlock_block => \A req \in requests: ~ENABLED Withdraw(req[1]))
\* 3.2. 
UnlockTimeOnlyIncrease ==
    [][unlock_block <= unlock_block']_unlock_block
\* 3.3. 
OnlyTierOneCanLock ==
    [](\A address \in ADDRESSES: address \notin tier_one_addresses 
        => \A new_unlock_block \in 0..MAX_BLOCK_NUMBER: ~ENABLED Lock(address, new_unlock_block))
\* 3.4.
OnlyTierOneCanRemoveTierTwo ==
    [](\A address \in ADDRESSES: address \notin tier_one_addresses 
        => \A address2 \in ADDRESSES: ~ENABLED RemoveTierTwoAddress(address, address2))
\* 3.5.  
OnlyTierOneCanAddTierTwo ==
    [](\A address \in ADDRESSES: address \notin tier_one_addresses 
        => \A address2 \in ADDRESSES: ~ENABLED AddTierTwoAddress(address, address2))

\* 4. Tier-one minimization layer
\* 4.1.
BalanceEnoughtToWithdrawAll ==
    [](balance[OWNER_ADDRESS] >= Sum)
\* 4.2.
CannotSendMoneyToItself ==
    [](\A r \in requests: r[5] /= OWNER_ADDRESS)
\* 4.3.
CannotSendMoneyToZero ==
    [](\A r \in requests: r[5] /= 0)
\* 4.4.
RemovingTierTwoRemovesItsRequests ==
    [](block_number < MAX_BLOCK_NUMBER => 
        \A <<address1, address2>> \in tier_one_addresses \X tier_two_addresses: 
            ENABLED (
                /\ RemoveTierTwoAddress(address1, address2) 
                /\ ~\E req \in requests': req[4] = address2))



--------------------------------------

ADDRESSES_const == 0..(MAX_BLOCK_NUMBER+2)
NETWORK_ADDRESSES_const == 1..3
MONEY_const == 1..BALANCE_LIMIT
REQUEST_IDS_const == 0..MAX_BLOCK_NUMBER

====