class{:autocontracts} Pilha
{
    ghost var conteudo: seq<nat>;

    var vetor: array<nat>;

    var length : nat;

    var maxSize : nat;

    predicate Valid()
    {
        maxSize > 0
        && 0 <= length <= vetor.Length
        && vetor.Length == maxSize
        && vetor[0..length] == conteudo
        && length == |conteudo|
    }
    constructor (n:nat)
    requires n > 0
    ensures conteudo == []
    ensures length == 0
    ensures maxSize == n
    requires n > 0
    {
        maxSize := n;
        vetor := new nat[n];
        length := 0;
        conteudo := [];
    }

    //Adicionar um elemento no topo pilha e retornar verdadeiro, caso adicionado, ou falso, 
    //caso a pilha já esteja cheia.
    method push(e:nat) returns (b:bool)
    ensures old(length) == maxSize ==> (b == false) && (conteudo == old(conteudo)) && (length == old(length))
    ensures old(length) < maxSize ==> (b == true) && (conteudo == old(conteudo) + [e]) && (length == old(length) + 1) 
    && maxSize == old(maxSize) && vetor[old(length)] == e
    {
        b := false;

        if (length < maxSize)
        {
            conteudo := conteudo + [e];
            vetor[length] := e;
            length := length + 1;
            b := true;
        }

        return b;
    }

    //Remover um elemento do topo da pilha, caso ela não esteja vazia.
    method remove() returns ()
    requires length > 0
    ensures length == old(length) - 1
    {
        length := length - 1;
        conteudo := vetor[..length];
    }

    //Ler o valor do topo da pilha, sem removê-lo
    method peek() returns(e:nat)
    requires length > 0
    ensures length == old(length)
    ensures e == vetor[length-1]
    {
        e:=vetor[length-1];
        return e;
    }

    //Verificar se a pilha está cheia ou não, retornando verdadeiro ou falso
    method isFull() returns(b:bool)
    ensures b <==> length == maxSize
    {
        if(length == maxSize){
            return true;
        }else{
            return false;
        }
    }
    //Verificar se a pilha está vazia ou não, retornando verdadeiro ou falso.
    method isEmpty() returns(b:bool)
    ensures b <==> length == 0
    //ensures length == 0 ==> b == true
    //ensures length > 0 ==> b == false
    {
        if(length == 0){
            return true;
        }
        else{
            return false;
        }
    }

    //Informar o número de elementos armazenados na pilha.
    method getLength() returns (e:nat)
    ensures e == length
    {
        return length;
    }

    //Informar o tamanho máximo da pilha.
    method getMaxSize() returns (e:nat)
    ensures e == maxSize
    {
        return maxSize;
    }
    
    //Inverter a ordem dos elementos da pilha
    method reverse() returns()
    ensures length == old(length)
    ensures length > 0 ==> forall i :: 0 <= i < length ==> old(vetor[i]) == vetor[length-i-1] 
    {
        if (length > 0) 
        {
            var aux := new nat[maxSize];

            forall (i | 0 <= i < length)
            {
                aux[length-i-1] := vetor[i];
            }

            vetor := aux;
            conteudo := vetor[0..length];
        }
    }
}

method Main()
{
    var pilha := new Pilha(5);
    var isEmpty := pilha.isEmpty();
    assert isEmpty == true;

    var size := pilha.getLength();
    assert size == 0;

    var push := pilha.push(1);
    assert push == true;
    push := pilha.push(2);
    assert push == true;
    push := pilha.push(3);
    assert push == true;
    push := pilha.push(4);
    assert push == true;
    push := pilha.push(5);
    assert push == true;
    push := pilha.push(6);
    assert push == false;

    isEmpty := pilha.isEmpty();
    assert isEmpty == false;
    var peek := pilha.peek();
    assert peek == 5;
/*
    pilha.reverse()
    peek := pilha.peek();
    assert peek == 1;

    var isFull := pilha.isFull();
    assert isFull == true;

    pilha.remove()
    peek := pilha.peek();
    assert peek == 2;
    
    isFull := pilha.isFull();
    assert isFull == false;
    */
}