/* run.config
   OPT: -memory-footprint 1 -val -deps -out -input -lib-entry -main main -journal-disable
*/

int TAB[10];
int G,H,J;
void main () {
  if (H) {H= 3; J++;TAB[4]--;};
  if (J) G=6;
  if (G) H=1;
  if (H) {TAB[1]++; TAB[6]++;};
}
