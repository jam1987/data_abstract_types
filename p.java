class p {

public static void main(String[] args) {
int a[] = new int[5];
int i;
for (int k = 0; k < 5; k++)
a[k] = 10 * k + 7;
i = 1;
a[i++] = a[++i] = i++;

for (int k=0;k<5;k++) {
  System.out.println(a[k]);
}
}
}