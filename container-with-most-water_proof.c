/*@ 
    lemma l1:
    \forall integer i, j, a, b;
        0 <= i <= j && 0 <= a <= b ==> i*a <= j*a;
    
    lemma l2:
    \forall integer i, j, a, b;
        0 <= i <= j && 0 <= a <= b ==> j*a <= j*b;

    lemma merge:
    \forall integer i, j, a, b;
        0 <= i <= j && 0 <= a <= b ==> i*a <= j*a && j*a <= j*b ==> i*a <= j*b;

    lemma mainLemma:
        \forall integer i, j, a, b;
            0 <= i <= j && 0 <= a <= b ==> i*a <= j*b;
*/
/*@
    // precondition
    requires n >= 2;
    requires \valid(a+(0.. n-1));
    requires \forall integer j; 0 <= j < n ==> a[j] >= 0;

    // postcondition
    assigns \nothing;
    ensures \forall integer i, j; 0 <= i < j < n ==> \result >= (j-i) * \min(a[i], a[j]);
    ensures \exists integer i, j; 0 <= i < j < n ==> \result == (j-i) * \min(a[i], a[j]);
*/

int maxArea(int* a, int n) {
    int l = 0;
    int r = n - 1;
    int ans = 0;
    /*@
        loop invariant 0 <= l <= r < n;
        loop invariant \forall integer i,j; 0 <= i < l && i <= j < n ==> ans >= (j-i) * \min(a[i],a[j]);
        loop invariant \forall integer i,j; 0 <= i <= j && r < j < n ==> ans >= (j-i) * \min(a[i],a[j]);
        loop invariant \exists integer i,j; (0 <= i < l && i <= j < n ==> ans == (j-i) * \min(a[i],a[j])) || 
                         (0 <= i <= j && r < j < n ==> ans >= (j-i) * \min(a[i],a[j]));

        loop assigns l, r, ans;
        loop variant r - l;
    */

    while (l != r) {
        int current_ans = ans;
        int new_value = (r - l) * (a[l] < a[r] ? a[l] : a[r]);
        //@ assert new_value == (r - l) * \min(a[l], a[r]);
        if (new_value > current_ans) {
            ans = new_value;
        }
        //@ assert ans == \max(new_value, ans);
        if (a[l] < a[r]) {
            l++;
        }
        else {
            r--;
        }
    }
    return ans;
}