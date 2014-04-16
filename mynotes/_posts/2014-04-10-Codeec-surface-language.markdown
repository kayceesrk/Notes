---
layout: post
title:  "CoDeEc: A language for declarative programming under eventual consistency"
date:   2014-04-10 14:21:24
categories: Research Notes
---

Codeec provides a declarative language for describing and programming with
eventually consistent data types (ECDT). It provides a Haskell API for
describing CRDT-like ECDTs which are then mapped on top of Cassandra.

## Codeec API

The API is presented below. The article corresponds to [this][github-snapshot]
EC-debug development snapshot.

{% highlight haskell %}

module Codeec (

-------------------------------------------------
-- Types
-------------------------------------------------

-- Eventually consistent computation
type EC a = Database.Cassandra.CQL.Cas a
instance Monad EC

-- Operations on eventually consistent objects
type Proc a b
instance Monad (Proc a)

-- Operation Context
type Ctxt a = Data.Graph.Inductive.Tree.Gr a ()

-- Effect
class Database.Cassandra.CQL.CasType a => Effect a

type Table = String
type Sess  = UUID
type Key   = UUID

-------------------------------------------------
-- Functions
-------------------------------------------------

createTable :: Table -> EC ()
performOp   :: (Effect a, Show res)
            => (Ctxt a -> arg -> Proc a res) -- Operation definition
			-> Table
			-> Key
			-> arg
			-> EC res
effect      :: Effect a => a -> Proc a ()
runEC       :: Database.Cassandra.CQL.Pool -> EC a -> IO a
{% endhighlight %}

</br>
# Programming with Codeec - Bank Account

Let us describe an eventually consistent (unsafe) bank account. For the sake of
discussion, let us consider that the only mutable operations on the bank
account are **deposit** and **withdraw**, restricted whole dollar transactions. The
operations deposit and withdraw are the **effects** on the bank account. We can
describe the effects through the Haskell type:

{% highlight haskell %}
data BankAccount = Deposit Int | Withdraw Int deriving Show
{% endhighlight %}

Since our intention is to record the effects into Cassandra, we need to
implement serialization functions for the effect values. This is achieved by
making `BankAccount` and instance of `Effect` as follows:

{% highlight haskell %}
instance Serialize BankAccount where
  put (Deposit v) = putTwoOf S.put S.put (0::Word8, v)
  put (Withdraw v) = putTwoOf S.put S.put (1::Word8, v)
  get = do
    (i::Word8,v::Int) <- getTwoOf S.get S.get
    case i of
      0 -> return $ Deposit v
      1 -> return $ Withdraw v

instance CasType BankAccount where
  getCas = do
    r <- decode . unBlob <$> getCas
    case r of
      Left _ -> error "Parse fail"
      Right v -> return $ v
  putCas = putCas . Blob . encode
  casType _ = CBlob

instance Effect BankAccount
{% endhighlight %}

Since we are operating in an eventually consistent scenario, there might be
concurrent deposits or withdraws. Our application logic needs to
deterministically resolve such conflicting actions. The effects that are
visible to an operation is made visible through a value of type `Ctxt
BankAccount`, which is a **partial order** of the operations performed on a
particular account. The operations are defined as **folds** over this partially
ordered trace to produce a result, as well as produce any effects as a result.

With respect to our bank account ECDT, we will define three operations:
`deposit`, `withdraw`, and `getBalance`. The implementation of the operations
are given below:

{% highlight haskell %}
deposit :: Ctxt BankAccount -> Int -> Proc BankAccount ()
deposit _ amt = effect $ Deposit amt

withdraw :: Ctxt BankAccount -> Int -> Proc BankAccount Bool
withdraw ctxt amt = do
  bal <- getBalance ctxt ()
  if bal > amt
  then do
    effect $ Withdraw amt
    return True
  else do
    return False

getBalance :: Ctxt BankAccount -> () -> Proc BankAccount Int
getBalance ops () = do
  let v = foldl acc 0 $ labNodes ops
  return v
  where
    acc s (_::Int, Deposit i) = s + i
    acc s (_::Int, Withdraw i) = s - i
{% endhighlight %}

And, we are done. We can now use the bank account ECDT as follows:

{% highlight haskell %}
main = do
  pool <- newPool [("localhost", "9042")] "test"
  x <- randomIO
  runEC pool $ do
    createTable "BankAccount"

    performOp deposit "BankAccount" x 100
    v <- performOp getBalance "BankAccount" x ()
    liftIO $ putStrLn $ "After deposit 100. Balance = " ++ show v

    performOp deposit "BankAccount" x 200
    v <- performOp getBalance "BankAccount" x ()
    liftIO $ putStrLn $ "After deposit 200. Balance = " ++ show v

    s <- performOp withdraw "BankAccount" x 200
    v <- performOp getBalance "BankAccount" x ()
    liftIO $ putStrLn $ "After withdraw 200. Success? = "++ show s
						++ ". Balance = " ++ show v

    s <- performOp withdraw "BankAccount" x 200
    v <- performOp getBalance "BankAccount" x ()
    liftIO $ putStrLn $ "After withdraw 200. Success? = "++ show s
						++ ". Balance = " ++ show v
{% endhighlight %}

Assuming that you have a Cassandra server running on your local host that has a
keyspace called `test`, the output produced is:

	(CREATED,Keyspace "test",Table "bankaccount")
	After deposit 100. Balance = 100
	After deposit 200. Balance = 300
	After withdraw 200. Success? = True. Balance = 100
	After withdraw 200. Success? = False. Balance = 100

Notice that the last withdraw operation was a failure; this is expected since
the balance at this point was 100, and we are trying to withdraw 200.

# Consistency Specificaiton

Since the ECDT is replicated at multiple instances, potentially spread across
the globe, any operation performed on the store is not immediately seen by
another operation. If two withdraw operations are concurrently applied to the
same bank account, then there is a possibility of the **account balance dropping
below 0**.

The real situation is even worse; nosql systems such as Cassandra choose
availability over consistency (recall CAP theorem). There is no
guarantee that an operation (say deposit A) will be visible to subsequent
operations in the same session; the connection to the replica to which A was
applied to might become disconnected, and subsequent operations might be
applied to a different replica which has not yet seen A. And this is the reason
why consistency-critical applications such as bank accounts are not written
over nosql stores.

Our idea is to specify the application-level consistency guarantees as a
**specification**. The implementation enforces the specification such that they
are never violated at runtime. The details of the specification language, and
its associated consistency inference and enforcement mechanisms would have to
wait for another post.

[github-snapshot]: https://github.com/kayceesrk/ec-debug/tree/1d412bdee900d525cd5af80ce914d8310c9a6467
